module
public meta import Lean.Elab.Command
public meta import Quotify.BinRel
public meta import Quotify.Attribute

open Quotify Lean Elab Command

elab "#quotify_rel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo m!"[{binRel.numParams}] {binRel.expr}"

elab "#quotify_qrel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let quotRel ← binRel.quotify
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo quotRel

elab "#quotify_setoid " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let some inst ← binRel.getSetoid?
      | throwError "No setoid found for {indentExpr binRel.expr}"
    logInfo inst

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab "#quotify_theorems " rel?:(term)? : command => do
  let thms := extension.getState (← getEnv)
  if let some rel := rel? then
    withRef rel <| liftTermElabM do
      let binRel ← BinRel.fromTerm rel
      let some thms := thms[binRel]?
        | throwError "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
      let msg : MessageData := thms.map MessageData.ofConstName
      logInfo msg
  else
    for (binRel, thms) in thms do
      let thmsMsg : MessageData := thms.map MessageData.ofConstName
      logInfo m!"{binRel.expr}:\n{thmsMsg}"
