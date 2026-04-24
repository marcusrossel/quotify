module
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.Simp
public meta import Quotify.Attribute

open Lean Meta Elab Tactic Simp

meta def Lean.LocalContext.getVisibleFVarIds (lctx : LocalContext) : Array FVarId :=
  lctx.getFVarIds.filter fun fvarId => !(lctx.get! fvarId |>.isImplementationDetail)

namespace Quotify

-- **TODO** Swapping the relation need not be a separate step from pushing the quotients. We can
--          perform them all in a single simproc. Namely, once the swap-relation simproc applies it
--          calls the sub-simproc for pushing the quotients.

/--
Replaces all occurrences of `binRel` in the goal and local context with the corresponding quotient
equality relation, proven equal by `iffQuotEq`.
-/
meta def swapRelation (binRel : BinRel) (iffQuotEq : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    -- We use `simp only at *` instead of `rw`, so repeated rewrites occur automatically.
    let iffQuotEqSimpThm    ← SimpTheorems.add {} (.other `Quotify.swapRelation) binRel.levelParams.toArray iffQuotEq
    let simpCtx             ← Simp.mkContext (simpTheorems := #[iffQuotEqSimpThm])
    let lctx                ← getLCtx
    let fvarIdsToSimp      := lctx.getVisibleFVarIds
    let (some (_, goal), _) ← simpGoal goal simpCtx (fvarIdsToSimp := fvarIdsToSimp)
      | throwError "`quotify` failed to swap the relation {indentExpr binRel.expr}\nfor equality of \
                    quotients."
    replaceMainGoal [goal]

meta def pushQuotientsSimproc (thms : Extension.Theorems) : Simproc := fun e => do
  let_expr Quotient.mk _ setoid app := e | return .continue
  -- **TODO** This loop is very expensive at the moment.
  for (kind, thms) in thms do
    for thm in thms do
      let some prf ← thm.mkPush? app setoid kind | return .continue
      let_expr Eq _ _ pushed := ← inferType prf | return .continue
      return .visit { expr := pushed, proof? := prf }
  return .continue

meta def pushQuotients (binRel : BinRel) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let thms ← extension.getMatchingTheorems' binRel
    -- This follows parts of the implementation of `Command.elabSimprocPattern`. However, notably we
    -- do not register the simproc.
    let pattern : Expr ← elabTerm (← `(@Quotient.mk _ _ _)) none
    Term.synthesizeSyntheticMVars
    let keys ← withSimpGlobalConfig <| DiscrTree.mkPath pattern
    -- Runs the simproc.
    let simpCtx             ← Simp.mkContext Simp.neutralConfig
    let lctx                ← getLCtx
    let fvarIdsToSimp      := lctx.getVisibleFVarIds
    let simprocs           := Simprocs.addCore {} keys ``pushQuotientsSimproc (post := true) (.inl <| pushQuotientsSimproc thms)
    let (some (_, goal), _) ← simpGoal goal simpCtx #[simprocs] (fvarIdsToSimp := fvarIdsToSimp)
      | throwError "`quotify` failed to push quotients."
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
    pushQuotients binRel
