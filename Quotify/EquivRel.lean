module
public import Lean.Meta.Basic
public import Lean.Elab.Term
import Lean.Meta.Reduce

open Lean Meta Elab Term

namespace Quotify

-- TODO: Rename to BinRel
/--
An `EquivRel` represents an equivalence relation in the form `λ a₁ … aₙ, r a₁ … aₙ`, where `r` is a
potentially parametric equivalence relation, and the application `r a₁ … aₙ` yields a binary
relation. Some of the parameters of `r` may be applied. For example for equivalence of natural
numbers modulo a value, we can have the following `EquivRel`s:
* polymorphic: `λ m, EqMod m`
* applied: `EqMod 1`, `EqMod 2`, `EqMod 3`, ...
-/
public structure EquivRel where
  /-- The equivalence relation of the form `λ a₁ … aₙ, r a₁ … aₙ`. Note that `r a₁ … aₙ` can itself
      be a `λ` taking two arguments (the elements to be compared by the equivalence relation). That
      is, `a₁ … aₙ` are only the arguments parameterizing the relation. -/
  expr : Expr
  /-- Given that `expr` is `λ a₁ … aₙ, r a₁ … aₙ`, the type of `r a₁ … aₙ` is
      `(argType a₁ … aₙ) → (argType a₁ … aₙ) → Prop`. -/
  argType : Expr
  /-- The number of arguments parameterizing the relation. For `λ a₁ … aₙ, r a₁ … aₙ` where
      `r : α → α → Prop` we have `numParams = n`. If `r a₁ … aₙ` is itself a `λ` with two arguments,
      we get `λ a₁ … aₙ lhs rhs, … lhs rhs`, but still have `numParams = n`. -/
  numParams : Nat
  deriving BEq, Hashable, Inhabited

namespace EquivRel

/--
Given an expression of the form `α → α → Prop`, returns `α`, otherwise `none`.

Note: This function can easily fail if the given expression contains uninstantiated mvars or
      `mdata`, so make sure it is cleaned up beforehand accordingly.
-/
def homogenousBinaryRelationType? (type : Expr) : MetaM (Option Expr) := do
  let some (lhsType, rhs) := type.arrow? | return none
  let some (rhsType, prop) := rhs.arrow? | return none
  unless prop.isProp && lhsType == rhsType do return none
  return lhsType

inductive GetArgTypeResult where
  | success (argType : Expr)
  | illformedType (type : Expr)

/--
Given that `rel` has type `α → α → Prop` modulo `numParams` parameters, gets the argument type `α`
abstracted over the parameters.
-/
def getArgType (rel : Expr) (numParams : Nat) : MetaM GetArgTypeResult := do
  lambdaBoundedTelescope rel numParams fun fvars body => do
    let relType ← inferType body
    if let some argType ← homogenousBinaryRelationType? relType then
      let argType ← mkLambdaFVars fvars argType
      return .success argType
    else
      let failedRelType ← mkLambdaFVars fvars relType
      return .illformedType failedRelType

/--
Normalizes the names of level parameters in `expr`. We rename them to `_uvar.0`, `_uvar.1`, etc.
-/
def normalizeLevelParams (expr : Expr) : MetaM Expr := do
  let { params, .. } := collectLevelParams {} expr
  let normParams := params.mapIdx fun idx _ => mkLevelParam (.num `_uvar idx)
  return expr.instantiateLevelParamsArray params normParams

-- TODO: What sort of reduction does `reduce` actually perform? Is there something more principled
--       that we could apply, e.g. to obviate the need for the subsequent `eta`?
def reduceRelation (rel : Expr) : MetaM Expr := do
  let rel ← withReducibleAndInstances do reduce (skipTypes := false) rel
  return rel.eta

public inductive FromExprResult where
  | success (rel : EquivRel)
  | illformedType (type : Expr)

/--
Given a `rel` of type `α → α → Prop`, returns an equivalent `EquivRel` which fully applies `rel` up
to its final two arguments of type `α` and abstracts over all mvar arguments. That is, it returns
an expression of the form `λ m₁ … mₙ, rel m₁ … mₙ`, where `m₁ … mₙ` are the mvars in `rel`. As
`rel m₁ … mₙ` can itself be a `λ`, we keep track of how many arguments in the telescope parameterize
the relation in `EquivRel.numParams`. That
-/
def fromExpr (rel : Expr) : MetaM FromExprResult := do
  let rel ← instantiateMVars rel
  let rel ← reduceRelation rel
  -- Abstracts the relation over its parameters, which are (expected to be) represented as mvars. So
  -- from `rel ?m₁ … ?mₙ` we get `λ m₁ … mₙ => rel m₁ … mₙ`.
  let { expr := rel, mvars := relMVars, .. } ← abstractMVars rel
  -- The number of arguments parameterizing the equivalence relation.
  let numParams := relMVars.size
  -- This step ensures that the names of universe parameters in `rel` are consistent (note that
  -- `abstractMVars` above ensured that there are no level mvars). If we did not do this, then
  -- "obviously" equal `EquivRel`s would not compare as equal due to mismatching universe parameter
  -- names.
  let rel ← normalizeLevelParams rel
  -- Gets the argument type, while also checking that `rel` is a homogeneous binary relation.
  match ← getArgType rel numParams with
  | .success argType    => return .success { expr := rel, argType, numParams }
  | .illformedType type => return .illformedType type

public inductive FromFullyAppliedResult where
  | success (rel : EquivRel)
  | illformedType (type : Expr)
  | missingArgs (numArgs : Nat)

instance : Coe FromExprResult FromFullyAppliedResult where
  coe
    | .success rel        => .success rel
    | .illformedType type => .illformedType type

/--
Given an `expr` which reduces to the form `r a₁ … aₙ lhs rhs`, where `r a₁ … aₙ : α → α → Prop`,
returns an `EquivRel` for `r a₁ … aₙ`. See `EquivRel.fromExpr` for more information.

---

We extract the equivalence relation as follows.

1. We chop off the final two arguments, assuming they are the arguments being compared by the
   equivalence relation. Thus, the remaining expression is the equivalence relation.
2. In `fromExpr` we `reduce` the equivalence relation to normalize it as much as possible.

Note, we do not simply reduce the entire term initially, as this could cause us to lose the
distinction between the equivalence relation and its arguments. For example, consider the term
`(fun l₁ l₂, ∀ x, x ∈ l₁ ↔ x ∈ l₂) a b`. If we reduce this term immediately, we get
`∀ x, x ∈ a ↔ x ∈ b`, which is not an application containing the elements being compared, so it is
not immedaitely obvious what the equivalence relation should be.
-/
public def fromFullyApplied (app : Expr) : MetaM FromFullyAppliedResult := do
  -- We used to run `let app ← withConfig ({ · with beta := false }) do whnf app` at the start. This
  -- was supposed to unfold the head such that any potential arguments "hidden" in the head become
  -- visible. For example, given a definition `Empty {α} (l : List α) : Prop := l = []`, this
  -- unfolds the term `@Empty α l` to `@Empty (List α) l []`. Note that the term `@Empty α l` has
  -- two arguments, but they aren't the arguments being compared by the underlying equivalence
  -- relation `=`. However, this also reduced cases like `SetEq a b` to `∀ x, x ∈ a ↔ x ∈ b` where
  -- `SetEq {α} : Prop := fun (l₁ l₂ : List α), ∀ x, x ∈ l₁ ↔ x ∈ l₂`. This was problematic due to
  -- the reasons outlined in the documentation comment above. As a result, we now simply expect that
  -- the initial given term already distinguishes clearly between the equivalence relation and the
  -- arguments being compared. If this becomes an issue in the future, we should revisit this.
  let app := app.cleanupAnnotations
  let numArgs := app.getAppNumArgs'
  unless app.getAppNumArgs' ≥ 2 do return .missingArgs numArgs
  let rel := app.stripArgsN 2
  fromExpr rel

public def fromTerm (rel : Term) : TermElabM EquivRel := do
  let relExpr ← elabTerm rel none
  -- We η-expand the `relExpr` so that we always have binders for at least the two final arguments
  -- to the equivalence relation. This is important, so that when we subsequently
  -- `lambdaMetaTelescope` over this expression, we actually get mvars for the two arguments.
  let relExpr ← etaExpand relExpr
  let (_, _, fullyAppliedRelExpr) ← lambdaMetaTelescope relExpr
  match ← EquivRel.fromFullyApplied fullyAppliedRelExpr with
  | .success equivRel => return equivRel
  | .missingArgs numArgs =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a binary relation, but takes {numArgs} arguments."
  | .illformedType type =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a homogeneous binary relation, but is {indentExpr type}"

/--
Given `equivRel.expr` of the form `λ a₁ … aₙ, r a₁ … aₙ`, executes
`k : (params : Array Expr) → (rel : Expr) → (argType : Expr) → MetaM α` with `params` being fvars
for `a₁ … aₙ`, and `rel` and `argType` instantiated to `r params` and `argType params` respectively.
-/
def telescope (equivRel : EquivRel) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  lambdaBoundedTelescope equivRel.expr equivRel.numParams fun params rel => do
    let argType ← instantiateLambda equivRel.argType params
    k params rel argType

-- TODO: As we also need a proof of equivalence, this might need to be defined on some other type
--       than `EquivRel`.
-- TODO: Update the doc comment.
/--
Given an `EquivRel` of the form `λ a₁ … aₙ, r a₁ … aₙ`, returns the corresponding relation over
quotients `λ a₁ … aₙ lhs rhs, Quot.mk (r a₁ … aₙ) lhs = Quot.mk (r a₁ … aₙ) rhs`.
-/
public def quotify (equivRel : EquivRel) : MetaM Expr := do
  -- TODO: Construct a Setoid on the fly and use `Quotient`.
  equivRel.telescope fun params rel argType => do
    withLocalDecl `lhs .default argType fun lhs => do
      withLocalDecl `rhs .default argType fun rhs => do
        let eqLhs ← mkAppM ``Quot.mk #[rel, lhs]
        let eqRhs ← mkAppM ``Quot.mk #[rel, rhs]
        let eq ← mkEq eqLhs eqRhs
        let vars := params ++ #[lhs, rhs]
        mkLambdaFVars vars eq

-- TODO: Delete this if setoids become irrelevant. If it remains, make it more robust on errors.
public def getSetoid? (equivRel : EquivRel) : MetaM (Option Expr) := do
  lambdaTelescope equivRel.expr fun vars _ => do
    let mainType ← inferType vars.back!
    let level ← getLevel mainType
    let setoidType := mkApp (.const ``Setoid [level]) mainType
    let args := vars.pop.pop
    let synthType ← mkForallFVars args setoidType
    synthInstance? synthType

end EquivRel
