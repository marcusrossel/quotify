module
public import Lean.Meta.Basic
public import Lean.Elab.Term
import Lean.Meta.Reduce

open Lean Meta Elab Term

namespace Quotify

/--
A `BinRel` represents a binary relation in the form `λ a₁ … aₙ, r a₁ … aₙ`. Some of the parameters
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
  /-- The names of the level parameters over which `expr` (and `argType`) is abstracted. Note, this
      field is unrelated to `numParams`. -/
  levelParams : List Name
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

public structure LevelParamNormalization where
  original : List Name
  normal   : List Name

instance : EmptyCollection LevelParamNormalization where
  emptyCollection := { original := [], normal := [] }

/--
Normalizes the names of level parameters in `expr`. We rename them to `_uvar.0`, `_uvar.1`, etc.
-/
def normalizeLevelParams (expr : Expr) : MetaM (Expr × LevelParamNormalization) := do
  let { params, .. } := collectLevelParams {} expr
  let normNames := params.mapIdx fun idx _ => Name.num `_uvar idx
  let normParams := normNames.map mkLevelParam
  let expr := expr.instantiateLevelParamsArray params normParams
  let norm := { original := params.toList, normal := normNames.toList }
  return (expr, norm)

-- **TODO** What sort of reduction does `reduce` actually perform?
def reduceRelation (rel : Expr) : MetaM Expr := do
  let rel ← withReducibleAndInstances do reduce (skipTypes := false) rel
  return rel.eta

public inductive FromExprResult where
  | success (rel : BinRel) (levelParamNorm : LevelParamNormalization)
  | illformedType (type : Expr)

/--
Given a `rel` of type `α → α → Prop`, returns an equivalent `BinRel` which fully applies `rel` up
to its final two arguments of type `α` and abstracts over all mvar arguments. That is, it returns
an expression of the form `λ m₁ … mₙ, rel m₁ … mₙ`, where `m₁ … mₙ` are the mvars in `rel`. As
`rel m₁ … mₙ` can itself be a `λ`, we keep track of how many arguments in the telescope parameterize
the relation in `BinRel.numParams`. That
-/
public def fromExpr (rel : Expr) (normalize := true) : MetaM FromExprResult := do
  let rel ← instantiateMVars rel
  let rel ← if normalize then reduceRelation rel else pure rel
  -- Abstracts the relation over its parameters, which are (expected to be) represented as mvars. So
  -- from `rel ?m₁ … ?mₙ` we get `λ m₁ … mₙ => rel m₁ … mₙ`.
  let { expr := rel, mvars := relMVars, .. } ← abstractMVars rel
  -- The number of arguments parameterizing the binary relation.
  let numParams := relMVars.size
  -- This step ensures that the names of level parameters in `rel` are consistent (note that
  -- `abstractMVars` above ensured that there are no level mvars). If we did not do this, then
  -- "obviously" equal `BinRel`s would not compare as equal due to different level parameter names.
  let (rel, levelParamNorm) ← if normalize then normalizeLevelParams rel else pure (rel, ∅)
  -- Gets the argument type, while also checking that `rel` is a homogeneous binary relation.
  match ← getArgType rel numParams with
  | .illformedType type =>
    return .illformedType type
  | .success argType =>
    let levelParams := levelParamNorm.normal
    return .success { expr := rel, argType, numParams, levelParams } levelParamNorm

public inductive FromFullyAppliedResult where
  | success (rel : BinRel) (levelParamNorm : LevelParamNormalization)
  | illformedType (type : Expr)
  | missingArgs (numArgs : Nat)

instance : Coe FromExprResult FromFullyAppliedResult where
  coe
    | .success rel levelParamNorm => .success rel levelParamNorm
    | .illformedType type         => .illformedType type

/--
Given an `expr` which reduces to the form `r a₁ … aₙ lhs rhs`, where `r a₁ … aₙ : α → α → Prop`,
returns a `BinRel` for `r a₁ … aₙ`. See `BinRel.fromExpr` for more information.

Note, when `normalizeLevels = true` the types of `lhs` and `rhs` will still not be level-normalized.

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
public def fromFullyApplied (app : Expr) (normalize := true) : MetaM FromFullyAppliedResult := do
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
  fromExpr rel normalize

public def fromTerm (rel : Term) : TermElabM BinRel := do
  let relExpr ← elabTerm rel none
  -- We η-expand the `relExpr` so that we always have binders for at least the two final arguments
  -- to the binary relation. This is important, so that when we subsequently `lambdaMetaTelescope`
  -- over this expression, we actually get mvars for the two arguments.
  let relExpr ← etaExpand relExpr
  let (_, _, fullyAppliedRelExpr) ← lambdaMetaTelescope relExpr
  match ← BinRel.fromFullyApplied fullyAppliedRelExpr with
  | .success binRel _ => return binRel
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

/--
Given `binRel.expr` of the form `λ a₁ … aₙ, r a₁ … aₙ`, instantiates the binders with mvars and
returns `(params : Array Expr) × (lmvars : List Level) × (rel : Expr) × (argType : Expr)` with
`params` being the mvars for `a₁ … aₙ`, `lmvars` being the the level mvars instantiated for
`binRel.levelParams`, and `rel` and `argType` begin instantiated to `r params` and `argType params`
and the level mvars respectively.

If `levels := false`, level parameters will not be instantiated with level mvars.
-/
public def metaTelescope (binRel : BinRel) (levels := true) :
    MetaM (Array Expr × List Level × Expr × Expr) := do
  let mut expr := binRel.expr
  let mut argType := binRel.argType
  let mut freshLMVars := []
  -- It's important that we instantiate the level params with level mvars *before* we telescope, as
  -- otherwise the types of the created (expr) mvars still refer to the level params.
  if levels then
    freshLMVars ← mkFreshLevelMVars binRel.levelParams.length
    expr       := binRel.expr.instantiateLevelParams binRel.levelParams freshLMVars
    argType    := binRel.argType.instantiateLevelParams binRel.levelParams freshLMVars
  let (params, _, rel) ← lambdaMetaTelescope expr (maxMVars? := binRel.numParams)
  argType              ← instantiateLambda argType params
  return (params, freshLMVars, rel, argType)

public def synthSetoid? (binRel : BinRel) : MetaM (Option Expr) := do
  binRel.telescope fun params _ argType => do
    let level ← getLevel argType
    let setoidType := mkApp (.const ``Setoid [level]) argType
    let instanceType ← mkForallFVars params setoidType
    synthInstance? instanceType

theorem iff_quotient_eq (rel : α → α → Prop) (equiv : Equivalence rel) :
    ∀ lhs rhs, rel lhs rhs ↔ (Quotient.mk ⟨rel, equiv⟩ lhs = .mk ⟨rel, equiv⟩ rhs) :=
  fun _ _ => ⟨(Quotient.sound ·), (Quotient.exact ·)⟩

/--
Returns a proof of `BinRel.iff_quotient_eq` instantiated for the given `BinRel` and equivalence
proof. If the relation is not fully applied, the proof remains abstracted over the remaining
parameters. That is, it has type `∀ a₁ … aₙ, ∀ lhs rhs, binRel lhs rhs ↔ ⟦lhs⟧ = ⟦rhs⟧`.
-/
public def mkIffQuotientEq (binRel : BinRel) (equiv : Expr) : MetaM Expr := do
  binRel.telescope fun params rel argType => do
    let equiv  ← instantiateLambda equiv params
    let level  ← getLevel argType
    let proof := mkApp3 (.const ``iff_quotient_eq [level]) argType rel equiv
    mkLambdaFVars params proof

public structure Match where
  params : Array Expr
  levels : List Level

/--
Tries to match a given `target` against a `pattern` up to definitional equality. If the match
succeeds a substitution (a `Match`) for `target`'s parameters is returned.

Matching is asymmetric in that the `pattern` must be more abstract than the `target`. For example,
`pattern.expr = λ α, @List.Param α` will match `target.expr = @List.Param Nat`, but not the other
way around.

If `target` is not fully applied, i.e. it contains abstracted parameters, then the resulting `Match`
will contain mvars for these parameters. In contrast, level parameters will not be replaced by level
mvars.
-/
public def match? (pattern target : BinRel) : MetaM (Option Match) := do
  -- We do not want to instantiate the `target`'s level parameters with level mvars, as its level
  -- parameters are suited to "travel between contexts".
  let (_, _, target, _) ← target.metaTelescope (levels := false)
  -- We bump the mvar context depth so that only `pattern`s (abstracted) parameters can be matched
  -- but not the other way around. For example, this means that `@List.Param ?α` can be matched
  -- against `@List.Param Nat`, but not vice versa.
  withNewMCtxDepth do
    let (params, lmvars, pattern, _) ← pattern.metaTelescope
    if ← isDefEq pattern target then
      let params ← params.mapM instantiateMVars
      let levels ← lmvars.mapM instantiateLevelMVars
      return some { params, levels }
    else
      return none

end BinRel
