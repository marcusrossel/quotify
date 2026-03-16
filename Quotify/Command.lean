module
public meta import Lean.Elab.Command
public meta import Quotify.Attribute

open Quotify Lean Elab Command

elab tk:"#quotify_norm " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    withOptions (·.set `pp.fieldNotation.generalized false) do
      logInfoAt tk m!"[{binRel.numParams}] {binRel.expr}"

elab tk:"#quotify_equiv " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let info ← extension.info
    -- **TODO** let (equiv?, _) ← info.getRelevantProofs binRel.expr
    match info.getEquiv? binRel with
    | some _ => logInfoAt tk "✅"
    | none   => logInfoAt tk "❌"

elab tk:"#quotify_quot " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let info ← extension.info
    -- **TODO** let (some equiv, _) ← info.getRelevantProofs binRel.expr
    let some equiv := info.getEquiv? binRel
      | throwErrorAt tk "The relation {indentExpr binRel.expr} has no corresponding \
                         `{.ofConstName ``Setoid}` marked with `[quotify]`."
    let quotRel ← binRel.toQuotient equiv
    logInfoAt tk quotRel

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab tk:"#quotify_theorems " rel?:(term)? : command => liftTermElabM do
  let info ← extension.info
  if let some rel := rel? then
    withRef rel do
      let binRel ← BinRel.fromTerm rel
      let (_, compatThms) ← info.getRelevantProofs binRel.expr
      if compatThms.isEmpty then
        throwErrorAt tk "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
      let msg : MessageData := compatThms.map MessageData.ofConstName
      logInfoAt tk msg
  else
    for (binRel, { compatThms, .. }) in info do
      let thmsMsg : MessageData := compatThms.map MessageData.ofConstName
      logInfoAt tk m!"{binRel.expr}:\n{thmsMsg}"
