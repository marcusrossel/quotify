module
public meta import Lean.Elab.Command
public meta import Quotify.BinRel
public meta import Quotify.Setoid
public meta import Quotify.Attribute

open Quotify Lean Elab Command

elab "#quotify_rel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo m!"[{binRel.numParams}] {binRel.expr}"

/-
elab "#quotify_qrel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let quotRel ← quotify binRel
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo quotRel
-/

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab tk:"#quotify_theorems " rel?:(term)? : command => liftTermElabM do
  let info ← extension.info
  if let some rel := rel? then
    withRef rel do
      let binRel ← BinRel.fromTerm rel
      let some proofs := info[binRel]?
        | throwErrorAt tk "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
      let msg : MessageData := proofs.compatThms.map MessageData.ofConstName
      logInfoAt tk msg
  else
    for (binRel, { compatThms, .. }) in info do
      let thmsMsg : MessageData := compatThms.map MessageData.ofConstName
      logInfoAt tk m!"{binRel.expr}:\n{thmsMsg}"
