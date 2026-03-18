module
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.Simp
public meta import Quotify.Attribute
public meta import Quotify.Lean

open Lean Meta Elab Tactic

namespace Quotify

-- **BUG** If we run in a reverted context, then `binRel` may contain fvars from the outer context.

/--
Replaces all occurrences of `binRel` in the goal and local context with the corresponding quotient
equality relation, proven equal by `iffQuotEq`.
-/
meta def swapRelation (binRel : BinRel) (iffQuotEq : Expr) : TacticM Unit :=
  -- We use `simp only` instead of `rw`, so that *all* occurrences are rewritten.
  inRevertedCtx do
    let goal             ← getMainGoal
    let iffQuotEqSimpThm ← SimpTheorems.add {} (.other `Quotify.swapRelation) binRel.levelParams.toArray iffQuotEq
    let simpCtx          ← Simp.mkContext (simpTheorems := #[iffQuotEqSimpThm])
    -- **TODO** Is this always type correct? Or can we run into "motive not type correct" issues?
    let (some (_, goal), _) ← simpGoal goal simpCtx
      | throwError "`quotify` failed to swap the relation {indentExpr binRel.expr}\nfor equality \
                    of quotients."
    replaceMainGoal [goal]

elab tk:"quotify" : tactic =>
  withRef tk <| withMainContext do
    let goalType ← getMainTarget
    let .success binRel _ ← BinRel.fromFullyApplied goalType (normalizeLevels := false)
      | throwError "`quotify` failed to find a binary relation in the goal."
    let some setoid ← extension.getMatchingSetoid? binRel
      | throwError "`quotify` failed to find a `{.ofConstName ``Setoid}` marked with `[quotify]` \
                     for the relation {indentExpr binRel.expr}"
    let iffQuotEq ← binRel.mkIffQuotientEq setoid.equiv.proof
    swapRelation binRel iffQuotEq
