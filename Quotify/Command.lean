module
public meta import Lean.Elab.Command
public meta import Quotify.EquivRel
public meta import Quotify.Attribute

open Quotify Lean Elab Command

elab "#quotify_rel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let equivRel ← EquivRel.fromTerm rel
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo m!"[{equivRel.numParams}] {equivRel.expr}"

elab "#quotify_qrel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let equivRel ← EquivRel.fromTerm rel
    let quotRel ← equivRel.quotify
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo quotRel

elab "#quotify_setoid " rel:term : command =>
  withRef rel <| liftTermElabM do
    let equivRel ← EquivRel.fromTerm rel
    let some inst ← equivRel.getSetoid?
      | throwError "No setoid found for {indentExpr equivRel.expr}"
    logInfo inst

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab "#quotify_theorems " rel?:(term)? : command => do
  let thms := extension.getState (← getEnv)
  if let some rel := rel? then
    withRef rel <| liftTermElabM do
      let equivRel ← EquivRel.fromTerm rel
      let some thms := thms[equivRel]?
        | throwError "No `quotify` theorems have been registered for {indentExpr equivRel.expr}"
      let msg : MessageData := thms.map MessageData.ofConstName
      logInfo msg
  else
    for (equivRel, thms) in thms do
      let thmsMsg : MessageData := thms.map MessageData.ofConstName
      logInfo m!"{equivRel.expr}:\n{thmsMsg}"
