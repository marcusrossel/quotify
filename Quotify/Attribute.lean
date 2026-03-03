module
public import Lean.Elab.Command
public meta import Quotify.Extension
meta import Lean.Elab.Command
import Quotify.Extension

open Lean Meta

namespace Quotify

inductive BodyUnfoldingResult where
  | setoid (e : Expr)
  | failure (e : Expr)

partial def getSetoidFromBody? (body : Expr) : MetaM BodyUnfoldingResult := do
  match_expr body with
  | Setoid.r _ setoid _ _ =>
    return .setoid setoid
  | _ =>
    let some unfoldedBody ← unfoldProjInst? body | return .failure body
    getSetoidFromBody? unfoldedBody

partial def setoidNameForDecl! (declName : Name) : MetaM Name := do
  let .thmInfo thmInfo ← getConstInfo declName
    | throwError "You can only use the `[quotify]` attribute on theorems, but \
                  `{.ofConstName declName}` is not a theorem."
  let thmType := thmInfo.type
  forallTelescope thmType fun _ body => do
    match ← getSetoidFromBody? body with
    | .setoid setoid =>
      if let some setoidName := setoid.getAppFn'.constName? then
        return setoidName
      else
        throwSetoidError m!"Additionally, the type of the setoid must be an application where the \
                            head is a constant. Howewer, the given setoid is `{setoid}`."
    | .failure body =>
      throwSetoidError m!"However, the given theorem `{.ofConstName declName}` reduces to `{body}`."
where
  throwSetoidError {α} (msgSuffix : MessageData) : MetaM α :=
    throwError "You can only use the `[quotify]` attribute on theorems of the form \
                `∀ …, lhs ≈ rhs` where `≈` involves a `Setoid` instance. Specifically, `lhs ≈ rhs` \
                must reduce to the form `Setoid.r … lhs rhs`. {msgSuffix}"

def addQuotifyAttribute (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  recordExtraModUseFromDecl (isMeta := false) declName
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  let setoidName ← setoidNameForDecl! resolvedDeclName
  extension.add { key := setoidName, val := resolvedDeclName } attrKind

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name := `quotify
    descr := "The `[quotify]` attribute is used to annotate theorems which prove compatability of \
              a given function with a given equivalence relation."
    applicationTime := .afterCompilation
    add declName stx attrKind := MetaM.run' <| withRef stx <| addQuotifyAttribute declName attrKind
  }

-- TODO: Move this to `Extension.lean`.
elab "#quotify " setoid:ident : command => do
  let thms := extension.getState (← getEnv)
  let setoidName ← resolveGlobalConstNoOverload setoid
  let some thms := thms[setoidName]?
    | throwError "No `quotify` theorems have been registered for `{.ofConstName setoid.getId}`."
  let msg : MessageData := thms.map MessageData.ofConstName
  logInfo msg

end Quotify
