import Lean
import Mathlib

open Lean Elab Tactic Term Meta

/-Prints out the current Environment.
-/
def printEnv : CoreM Unit := do
  let env ← getEnv
  for (name, info)
    in (env.constants).toList.take 150 do
        let type := info.type
        logInfo s!"{name} : {type}"
elab "printEnv" : tactic => do printEnv

/-Prints out the current Local-Context
-/
def printLocalCtxt : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let localCtxt ← getLCtx
    for localDecl in localCtxt do
        let expr := localDecl.toExpr
        let name := localDecl.userName
        let type := localDecl.type
        logInfo s!"{name} := {expr}"
        logInfo s!": {type}"
        logInfo " "
    logInfo " "
    logInfo s!"goal"
    logInfo s!": {←goal.getType}"
elab "printLocalCtxt" : tactic => do printLocalCtxt

/--
  `hide h` removes the given hypotheses from the *pretty-printed*
  goal state, but they remain usable by name in the proof.
-/
elab "hide " n:ident : tactic => do
  withMainContext do
    let n         := (n.getId)
    let goal      := ← getMainGoal
    let localCtxt := ← getLCtx
    let some fvar := localCtxt.findFromUserName? n | throwError s!"{n} is not in Local-Context!"
    goal.setFVarKind (fvar.fvarId) (LocalDeclKind.implDetail)


-- Example usage
example (p q r : Prop) (h : p → q) (h' : q → r) (hp : p) : r := by
  /- Goal state initially:
  p q r : Prop
  h : p → q
  h' : q → r
  hp : p
  ⊢ r
  -/
  hide hp
  /- After `hide hp`, goal state:
  p q r : Prop
  h : p → q
  h' : q → r
  ⊢ r
  -/
  exact h' (h hp)
