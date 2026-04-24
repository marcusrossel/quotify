module
public meta import Lean.Elab.Command
public meta import Quotify.Attribute

open Quotify Lean Meta Elab Command

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
    if let some setoid ← extension.getMatchingSetoid? binRel then
      logInfo <| .ofConstName setoid.declName
    else
      throwError "The relation {indentExpr binRel.expr}\nhas no matching `{.ofConstName ``Setoid}` \
                  marked with `[quotify]`."

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
    let some { equiv, .. } ← extension.getMatchingSetoid? binRel
      | throwError "The relation {indentExpr binRel.expr}\nhas no matching \
                         `{.ofConstName ``Setoid}` marked with `[quotify]`."
    let relIffQuotientEqProof ← binRel.mkIffQuotientEq equiv.proof
    let quotRel ← Meta.inferType relIffQuotientEqProof
    logInfo quotRel

/-- Shows the theorems used to push quotients for the given relation when calling `quotify.` -/
elab tk:"#quotify_push " rel:term : command =>
  withRef tk <| liftTermElabM do
    let binRel ← BinRel.fromTerm rel
    let thms ← extension.getMatchingTheorems' binRel
    unless !thms.isEmpty do
      throwError "No `quotify` theorems have been registered for {indentExpr binRel.expr}"
    let some setoid ← extension.getMatchingSetoidInstance? binRel
      | throwError "The relation {indentExpr binRel.expr}\nhas no matching \
                    `{.ofConstName ``Setoid}` marked with `[quotify]`."
    -- The setup here is a bit annoying, as `Theorem.mkPush?` expects the `setoid` to be ground and
    -- requires an `app` expression that matches `thm.fn`. As the `binRel` and each `Theorem` might
    -- be parameterized, we thus telescope into the `binRel` and instantiate the `setoid` and
    -- `thm.fn` with the `params` (note that `thm.fn` may already be partially instantiated by
    -- virtue of `getMatchingTheorems'`). We then construct an application for the given `fn` with
    -- mvars as arguments.
    binRel.telescope fun params _ argType => do
      let setoid ← instantiateLambda setoid params
      let mut msg : MessageData := .nil
      for (kind, thms) in thms do
        for thm in thms do
          let fn        ← instantiateLambda thm.fn params
          let argsMVars ← kind.freshArgMVars argType
          let app      := mkAppN fn argsMVars
          let some push ← thm.mkPush? app setoid kind | throwError "Internal error in `#quotify_push`."
          let push      ← mkLambdaFVars (params ++ argsMVars) push
          msg          := msg ++ m!"{.ofConstName thm.declName}: {push}\n"
      logInfo msg
