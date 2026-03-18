module
public import Lean.Elab.Tactic

open Lean Elab Tactic

namespace Lean

def LocalContext.getVisibleFVarIds (lctx : LocalContext) : Array FVarId :=
  lctx.getFVarIds.filter fun fvarId => !(lctx.get! fvarId |>.isImplementationDetail)

/--
Runs a given tactic `t` on the current goal with all (user-facing) fvars reverted, and reintroduces
the fvars afterwards.

This function assumes that `t` does not change the number of binders in the goal.
-/
public def Elab.Tactic.inRevertedCtx (t : TacticM α) : TacticM α := do
  -- Revert all fvars.
  let lctx      ← getLCtx
  let fvarIds  := lctx.getVisibleFVarIds
  let fvarNames ← fvarIds.mapM (·.getUserName)
  let goal      ← getMainGoal
  let (_, goal) ← goal.revert fvarIds (preserveOrder := true)
  replaceMainGoal [goal]
  -- Run `k` in the context of the reverted goal.
  goal.withContext do
    let result ← t
    -- Move into the context of the goal produced by `k`.
    let goal ← getMainGoal
    goal.withContext do
      -- Reintroduce the fvars reverted above. Note, this assumes that `k` did not modify the number
      -- of binders in the goal.
      let (_, goal) ← goal.introN fvarNames.size fvarNames.toList
      replaceMainGoal [goal]
      return result
