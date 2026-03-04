module
public import Lean.Elab.Command
import Lean.Expr
import Lean.Meta.Reduce

open Lean Meta

namespace Quotify

/--
An `EquivRel` represents an equivalence relation in the form `λ a₁ … aₙ lhs rhs, r a₁ … aₙ lhs rhs`,
where `r` is a potentially parametric equivalence relation, and the application `r a₁ … aₙ` yields a
binary relation. That is, we always expect the final two parameters of `r` to be the arguments to be
compared. Some of the parameters of `r` may be applied. For example for equivalence of natural
numbers modulo a value, we can have the following `EquivRel`s:
* polymorphic: `λ m lhs rhs, EqMod m lhs rhs`
* applied: `λ lhs rhs, EqMod 2 lhs rhs`, `λ lhs rhs, EqMod 42 lhs rhs`, ...

Note: While the abstraction over `lhs` and `rhs` could be dropped, we keep it for uniformity of the
      representation. For example, this way we always know that an `EquivRel` is an `Expr.lam`.
-/
public abbrev EquivRel := Expr

namespace EquivRel

/--
Given an expression of the form `α → α → Prop`, returns `α`, otherwise `none`.
-/
def homogenousBinaryRelationType? (type : Expr) : MetaM (Option Expr) := do
  let some (lhsType, rhs) := type.arrow? | return none
  let some (rhsType, prop) := rhs.arrow? | return none
  unless prop.isProp && lhsType == rhsType do return none
  return lhsType

public inductive FromExprResult where
  | success (rel : EquivRel)
  | illformedType (type : Expr)

/--
Given an `expr` of type `α → α → Prop`, returns an equivalent `EquivRel` which fully applies `expr`
and abstracts over all mvar arguments. That is, it returns an expression of the form
`λ m₁ … mₙ lhs rhs, expr m₁ … mₙ lhs rhs`, where `m₁ … mₙ` are the mvars in `expr`, and `lhs` and
`rhs` have type `α`.
-/
def fromExpr (expr : Expr) : MetaM FromExprResult := do
  let expr ← instantiateMVars expr
  let type ← inferType expr
  let some argType ← homogenousBinaryRelationType? type | return .illformedType type
  -- Given that `expr` has type `α → α → Prop`, constructs `expr ?lhs ?rhs : Prop` so that
  -- subsequent abstraction includes bound variables for `?lhs` and `?rhs`.
  let lhsArg ← mkFreshExprMVar argType (userName := `lhs)
  let rhsArg ← mkFreshExprMVar argType (userName := `rhs)
  let expr := mkAppN expr #[lhsArg, rhsArg]
  let expr ← reduce (skipTypes := false) expr -- TODO
  let { expr, .. } ← abstractMVars expr
  -- This step ensures that the names of universe parameters in `expr` are consistent (note that
  -- `abstractMVars` above ensured that there are no level mvars). Specifically, we rename the
  -- universe parameters to `_uvar.0`, `_uvar.1`, etc. If we did not do this, then "obviously" equal
  -- `EquivRel`s would not compare as equal due to mismatching universe parameter names.
  let { params, .. } := collectLevelParams {} expr
  let normParams := params.mapIdx fun idx _ => mkLevelParam (.num `_uvar idx)
  let expr := expr.instantiateLevelParamsArray params normParams
  return .success expr

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

1. We construct the WHNF of `app` *without β-reduction*. This is supposed to unfold the head such
   that any potential arguments "hidden" in the head become visible. For example, given a definition
   `Empty {α} (l : List α) : Prop := l = []`, this unfolds the term `@Empty α l` to
   `@Empty (List α) l []`. Note that the term `@Empty α l` has two arguments, but they aren't the
   arguments being compared by the underlying equivalence relation `=`.
2. We chop off the final two arguments, assuming they are the arguments being compared by the
   equivalence relation. Thus, the remaining expression is the equivalence relation.
3. In `fromExpr` we `reduce` the equivalence relation to normalize it as much as possible.

Note, we do not simply reduce the entire term initially, as this could cause us to lose the
distinction between the equivalence relation and its arguments. For example, consider the term
`(fun l₁ l₂, ∀ x, x ∈ l₁ ↔ x ∈ l₂) a b`. If we reduce this term immediately, we get
`∀ x, x ∈ a ↔ x ∈ b`, which is not an application containing the elements being compared, so it is
not immedaitely obvious what the equivalence relation should be.
-/
public def fromFullyApplied (app : Expr) : MetaM FromFullyAppliedResult := do
  let app ← withConfig ({ · with beta := false }) do whnf app
  let numArgs := app.getAppNumArgs'
  unless numArgs ≥ 2 do return .missingArgs numArgs
  let rel := app.getAppPrefix (numArgs - 2)
  fromExpr rel

-- TODO: Delete this if setoids become irrelevant. If it remains, make it more robust on errors.
public def getSetoid? (equivRel : EquivRel) : MetaM (Option Expr) := do
  lambdaTelescope equivRel fun vars _ => do
    let mainType ← inferType vars.back!
    let level ← getLevel mainType
    let setoidType := mkApp (.const ``Setoid [level]) mainType
    let args := vars.pop.pop
    let synthType ← mkForallFVars args setoidType
    synthInstance? synthType

end EquivRel
