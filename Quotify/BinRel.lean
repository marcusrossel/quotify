module
public import Lean.Meta.Basic
public import Lean.Elab.Term
import Lean.Meta.Reduce

open Lean Meta Elab Term

namespace Quotify

/--
An `BinRel` represents a binary relation in the form `λ a₁ … aₙ, r a₁ … aₙ`. Some of the parameters
of `r` may be applied. For example for equivalence of natural numbers modulo a value, we can have
the following `BinRel`s:
* polymorphic: `λ m, EqMod m`
* applied: `EqMod 1`, `EqMod 2`, `EqMod 3`, ...
-/
public structure BinRel where
  /-- The binary relation of the form `λ a₁ … aₙ, r a₁ … aₙ`. Note that `r a₁ … aₙ` can itself be a
      `λ` taking two arguments (the elements to be compared by the binary relation). That is,
      `a₁ … aₙ` are only the arguments parameterizing the relation. -/
  expr : Expr
  /-- Given that `expr` is `λ a₁ … aₙ, r a₁ … aₙ`, the type of `r a₁ … aₙ` is
      `(argType a₁ … aₙ) → (argType a₁ … aₙ) → Prop`. -/
  argType : Expr
  /-- The number of arguments parameterizing the relation. For `λ a₁ … aₙ, r a₁ … aₙ` where
      `r : α → α → Prop` we have `numParams = n`. If `r a₁ … aₙ` is itself a `λ` with two arguments,
      we get `λ a₁ … aₙ lhs rhs, … lhs rhs`, but still have `numParams = n`. -/
  numParams : Nat
  deriving BEq, Hashable, Inhabited

namespace BinRel

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
  | success (rel : BinRel)
  | illformedType (type : Expr)

/--
Given a `rel` of type `α → α → Prop`, returns an equivalent `BinRel` which fully applies `rel` up
to its final two arguments of type `α` and abstracts over all mvar arguments. That is, it returns
an expression of the form `λ m₁ … mₙ, rel m₁ … mₙ`, where `m₁ … mₙ` are the mvars in `rel`. As
`rel m₁ … mₙ` can itself be a `λ`, we keep track of how many arguments in the telescope parameterize
the relation in `BinRel.numParams`. That
-/
def fromExpr (rel : Expr) : MetaM FromExprResult := do
  let rel ← instantiateMVars rel
  let rel ← reduceRelation rel
  -- Abstracts the relation over its parameters, which are (expected to be) represented as mvars. So
  -- from `rel ?m₁ … ?mₙ` we get `λ m₁ … mₙ => rel m₁ … mₙ`.
  let { expr := rel, mvars := relMVars, .. } ← abstractMVars rel
  -- The number of arguments parameterizing the binary relation.
  let numParams := relMVars.size
  -- This step ensures that the names of universe parameters in `rel` are consistent (note that
  -- `abstractMVars` above ensured that there are no level mvars). If we did not do this, then
  -- "obviously" equal `BinRel`s would not compare as equal due to mismatching universe parameter
  -- names.
  let rel ← normalizeLevelParams rel
  -- Gets the argument type, while also checking that `rel` is a homogeneous binary relation.
  match ← getArgType rel numParams with
  | .success argType    => return .success { expr := rel, argType, numParams }
  | .illformedType type => return .illformedType type

public inductive FromFullyAppliedResult where
  | success (rel : BinRel)
  | illformedType (type : Expr)
  | missingArgs (numArgs : Nat)

instance : Coe FromExprResult FromFullyAppliedResult where
  coe
    | .success rel        => .success rel
    | .illformedType type => .illformedType type

/--
Given an `expr` which reduces to the form `r a₁ … aₙ lhs rhs`, where `r a₁ … aₙ : α → α → Prop`,
returns an `BinRel` for `r a₁ … aₙ`. See `BinRel.fromExpr` for more information.

---

We extract the binary relation as follows.

1. We chop off the final two arguments, assuming they are the arguments being compared by the binary
   relation. Thus, the remaining expression is the binary relation.
2. In `fromExpr` we `reduce` the binary relation to normalize it as much as possible.

Note, we do not simply reduce the entire term initially, as this could cause us to lose the
distinction between the binary relation and its arguments. For example, consider the term
`(fun l₁ l₂, ∀ x, x ∈ l₁ ↔ x ∈ l₂) a b`. If we reduce this term immediately, we get
`∀ x, x ∈ a ↔ x ∈ b`, which is not an application containing the elements being compared, so it is
not immedaitely obvious what the binary relation should be.
-/
public def fromFullyApplied (app : Expr) : MetaM FromFullyAppliedResult := do
  -- We used to run `let app ← withConfig ({ · with beta := false }) do whnf app` at the start. This
  -- was supposed to unfold the head such that any potential arguments "hidden" in the head become
  -- visible. For example, given a definition `Empty {α} (l : List α) : Prop := l = []`, this
  -- unfolds the term `@Empty α l` to `@Empty (List α) l []`. Note that the term `@Empty α l` has
  -- two arguments, but they aren't the arguments being compared by the underlying binary relation
  -- `=`. However, this also reduced cases like `SetEq a b` to `∀ x, x ∈ a ↔ x ∈ b` where
  -- `SetEq {α} : Prop := fun (l₁ l₂ : List α), ∀ x, x ∈ l₁ ↔ x ∈ l₂`. This was problematic due to
  -- the reasons outlined in the documentation comment above. As a result, we now simply expect that
  -- the initial given term already distinguishes clearly between the binary relation and the
  -- arguments being compared. If this becomes an issue in the future, we should revisit this.
  let app := app.cleanupAnnotations
  let numArgs := app.getAppNumArgs'
  unless app.getAppNumArgs' ≥ 2 do return .missingArgs numArgs
  let rel := app.stripArgsN 2
  fromExpr rel

public def fromTerm (rel : Term) : TermElabM BinRel := do
  let relExpr ← elabTerm rel none
  -- We η-expand the `relExpr` so that we always have binders for at least the two final arguments
  -- to the binary relation. This is important, so that when we subsequently `lambdaMetaTelescope`
  -- over this expression, we actually get mvars for the two arguments.
  let relExpr ← etaExpand relExpr
  let (_, _, fullyAppliedRelExpr) ← lambdaMetaTelescope relExpr
  match ← BinRel.fromFullyApplied fullyAppliedRelExpr with
  | .success binRel => return binRel
  | .missingArgs numArgs =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a binary relation, but takes {numArgs} arguments."
  | .illformedType type =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a homogeneous binary relation, but is {indentExpr type}"

/--
Given `binRel.expr` of the form `λ a₁ … aₙ, r a₁ … aₙ`, executes
`k : (params : Array Expr) → (rel : Expr) → (argType : Expr) → MetaM α` with `params` being fvars
for `a₁ … aₙ`, and `rel` and `argType` instantiated to `r params` and `argType params` respectively.
-/
public def telescope (binRel : BinRel) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  lambdaBoundedTelescope binRel.expr binRel.numParams fun params rel => do
    let argType ← instantiateLambda binRel.argType params
    k params rel argType

end BinRel
