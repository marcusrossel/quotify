module
public meta import Lean.Elab.Command
public meta import Quotify.Attribute

open Quotify Lean Elab Command

/-- Shows how `quotify` normalizes a given binary relation. -/
elab tk:"#quotify_norm " rel:term : command =>
  withRef tk <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    withOptions (·.set `pp.fieldNotation.generalized false) do
      logInfo m!"[{binRel.numParams}] {binRel.expr}"

/-- Shows the (first matching) `Setoid` registered for the given binary relation. -/
elab tk:"#quotify_setoid " rel:term : command =>
  withRef tk <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let infos ← extension.infos
    if let some setoid ← infos.getMatchingSetoid? binRel then
      logInfo <| .ofConstName setoid.declName
    else
      throwError "The relation {indentExpr binRel.expr}\nhas no matching \
                       `{.ofConstName ``Setoid}` marked with `[quotify]`."

/--
Shows all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab tk:"#quotify_theorems " rel?:(term)? : command =>
  withRef tk <| liftTermElabM do
    let infos ← extension.infos
    if let some rel := rel? then
      let binRel ← BinRel.fromTerm rel
      let thms ← infos.getMatchingTheorems binRel
      if thms.isEmpty then
        throwError "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
      logInfo m!"{thms}"
    else
      let mut msg : MessageData := .nil
      for (binRel, { theorems := thms, .. }) in infos do
        let thmsMsg := if thms.isEmpty then m!"∅" else m!"{thms}"
        msg := msg ++ m!"{binRel.expr}:{indentD thmsMsg}\n"
      logInfo msg

/--
Shows the type of the proof used to replace the given relation with equality on quotients when
calling `quotify`.
-/
elab tk:"#quotify_quot " rel:term : command =>
  withRef tk <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let infos ← extension.infos
    let some { equiv, .. } ← infos.getMatchingSetoid? binRel
      | throwError "The relation {indentExpr binRel.expr}\nhas no matching \
                         `{.ofConstName ``Setoid}` marked with `[quotify]`."
    let relIffQuotientEqProof ← binRel.mkIffQuotientEq equiv.proof
    let quotRel ← Meta.inferType relIffQuotientEqProof
    logInfo quotRel

/-- Shows the theorems used to push quotients for the given relation when calling `quotify.` -/
elab tk:"#quotify_push " rel:term : command =>
  withRef tk <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let infos ← extension.infos
    let thms ← infos.getMatchingTheorems binRel
    let simpThms ← thms.simp
    if simpThms.isEmpty then
      throwError "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
    let mut msg : MessageData := .nil
    for thm in simpThms do
      msg := msg ++ m!"{.ofConstName thm.declName}: {thm.expr}\n"
    logInfo msg
