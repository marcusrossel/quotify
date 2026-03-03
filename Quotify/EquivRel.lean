module
public import Lean.Elab.Command
import Lean.Expr

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
  let type ← inferType expr
  let some argType ← homogenousBinaryRelationType? type | return .illformedType type
  -- Given that `expr` has type `α → α → Prop`, constructs `expr ?lhs ?rhs : Prop` so that
  -- subsequent abstraction includes bound variables for `?lhs` and `?rhs`.
  let lhsArg ← mkFreshExprMVar argType (userName := `lhs)
  let rhsArg ← mkFreshExprMVar argType (userName := `rhs)
  let expr := mkAppN expr #[lhsArg, rhsArg]
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
-/
public def fromFullyApplied (app : Expr) : MetaM FromFullyAppliedResult := do
    -- TODO: This can cause problems when WHNF reduces so far that we beta reduce into the relation
  --       and don't have an application with ≥ 2 args anymore. E.g. see SetEq.lean.
  --       A partial fix is to reduce only up to instances. But then something like
  --       (fun a b => ∀ x, ... a ... b ...) a₁ a₂ still reduces too much.
  --       We tried only reducing to whnf at the end, but that broke some things in Test.lean
  --       which forced us to instantiate mvars, and which also didnt reduce to List.Perm then.
  --       I don't understand why that is. perhaps if we figure that out, then performing only
  --       reducible whnf in the start and full whnf at the end is the solution.
  --
  --       What would be best? WHNF with a restriction that beta reduction should only ocurr within
  --       the head? We can simulate that by only whnf on the head, but that leads to problems too.
  let app ← whnf app
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
