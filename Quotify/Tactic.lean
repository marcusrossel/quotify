module
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.Simp
public meta import Quotify.Attribute

open Lean Meta Elab Tactic

meta def Lean.LocalContext.getVisibleFVarIds (lctx : LocalContext) : Array FVarId :=
  lctx.getFVarIds.filter fun fvarId => !(lctx.get! fvarId |>.isImplementationDetail)

namespace Quotify

/--
Replaces all occurrences of `binRel` in the goal and local context with the corresponding quotient
equality relation, proven equal by `iffQuotEq`.
-/
meta def swapRelation (binRel : BinRel) (iffQuotEq : Expr) : TacticM Unit := do
  -- We use `simp only at *` instead of `rw`, so repeated rewrites occur automatically.
  let goal                ← getMainGoal
  let iffQuotEqSimpThm    ← SimpTheorems.add {} (.other `Quotify.swapRelation) binRel.levelParams.toArray iffQuotEq
  let simpCtx             ← Simp.mkContext (simpTheorems := #[iffQuotEqSimpThm])
  let lctx                ← getLCtx
  let fvarIdsToSimp      := lctx.getVisibleFVarIds
  let (some (_, goal), _) ← simpGoal goal simpCtx (fvarIdsToSimp := fvarIdsToSimp)
    | throwError "`quotify` failed to swap the relation {indentExpr binRel.expr}\nfor equality of \
                  quotients."
  replaceMainGoal [goal]

elab tk:"quotify" : tactic =>
  withRef tk <| withMainContext do
    let goalType ← getMainTarget
    -- We do not normalize the goal `binRel`, as otherwise `simp` may not be able to rewrite. For
    -- example, `simp` will not rewrite `≈` with lemmas about `List.Perm`.
    let .success binRel _ ← BinRel.fromFullyApplied goalType (normalize := false)
      | throwError "`quotify` failed to find a binary relation in the goal."
    let some setoid ← extension.getMatchingSetoid? binRel
      | throwError "`quotify` failed to find a `{.ofConstName ``Setoid}` marked with `[quotify]` \
                     for the relation {indentExpr binRel.expr}"
    let iffQuotEq ← binRel.mkIffQuotientEq setoid.equiv.proof
    swapRelation binRel iffQuotEq
