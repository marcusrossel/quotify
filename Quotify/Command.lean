module
public meta import Lean.Elab.Command
public meta import Quotify.Attribute

open Quotify Lean Elab Command

elab tk:"#quotify_norm " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    withOptions (·.set `pp.fieldNotation.generalized false) do
      logInfoAt tk m!"[{binRel.numParams}] {binRel.expr}"

elab tk:"#quotify_setoid " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let infos ← extension.infos
    if let some setoid ← infos.getMatchingSetoid? binRel then
      logInfoAt tk <| .ofConstName setoid.declName
    else
      throwErrorAt tk "The relation {indentExpr binRel.expr}\nhas no matching \
                       `{.ofConstName ``Setoid}` marked with `[quotify]`."

elab tk:"#quotify_quot " rel:term : command =>
  withRef rel <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let infos ← extension.infos
    let some { equiv, .. } ← infos.getMatchingSetoid? binRel
      | throwErrorAt tk "The relation {indentExpr binRel.expr}\nhas no matching \
                         `{.ofConstName ``Setoid}` marked with `[quotify]`."
    let relIffQuotientEqProof ← binRel.mkIffQuotientEq equiv.proof
    let quotRel ← Meta.inferType relIffQuotientEqProof
    logInfoAt tk quotRel

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab tk:"#quotify_theorems " rel?:(term)? : command => liftTermElabM do
  let infos ← extension.infos
  if let some rel := rel? then
    withRef rel do
      let binRel ← BinRel.fromTerm rel
      let thms ← infos.getMatchingTheorems binRel
      if thms.isEmpty then
        throwErrorAt tk "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
      -- **TODO** Figure out how to print the theorems with their kind.
      let msg : MessageData := thms.values.flatten.map (MessageData.ofConstName ·.declName)
      logInfoAt tk msg
  else
    for (binRel, { theorems := thms, .. }) in infos do
      -- **TODO** Figure out how to print the theorems with their kind.
      let thmsMsg : MessageData := thms.values.flatten.map (MessageData.ofConstName ·.declName)
      logInfoAt tk m!"{binRel.expr}:\n{thmsMsg}"
