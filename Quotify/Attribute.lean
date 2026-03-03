module
public import Lean.Elab.Command
public meta import Quotify.Extension
meta import Lean.Elab.Command
import Quotify.Extension
import Quotify.EquivRel

-- TODO: Combine this file with `Extension.lean`.

open Lean Meta Elab Term Command

namespace Quotify

partial def equivRelForDecl! (declName : Name) : MetaM EquivRel := do
  let .thmInfo thmInfo ← getConstInfo declName
    | throwError "You can only use the `[quotify]` attribute on theorems, but \
                  `{.ofConstName declName}` is not a theorem."
  let thmType := thmInfo.type
  let (_, _, fullyAppliedThmType) ← forallMetaTelescopeReducing thmType
  let .success equivRel ← EquivRel.fromFullyApplied fullyAppliedThmType
    | throwError "You can only use the `[quotify]` attribute on theorems of the form \
                  `∀ … lhs rhs, r … lhs rhs` where `r …` is a homogeneous binary relation."
  return equivRel

def addQuotifyAttribute (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  recordExtraModUseFromDecl (isMeta := false) declName
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  let equivRel ← equivRelForDecl! resolvedDeclName
  extension.add { key := equivRel, val := resolvedDeclName } attrKind

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name := `quotify
    descr := "The `[quotify]` attribute is used to annotate theorems which prove compatability of \
              a given function with a given equivalence relation."
    applicationTime := .afterCompilation
    add declName stx attrKind := MetaM.run' <| withRef stx <| addQuotifyAttribute declName attrKind
  }

meta def elabEquivRel (rel : Term) : TermElabM EquivRel := do
  let relExpr ← elabTerm rel none
  -- We η-expand the `relExpr` so that we always have binders for at least the two final arguments
  -- to the equivalence relation. This is important, so that when we subsequently
  -- `lambdaMetaTelescope` over this expression, we actually get mvars for the two arguments.
  let relExpr ← etaExpand relExpr
  let (_, _, fullyAppliedRelExpr) ← lambdaMetaTelescope relExpr
  match ← EquivRel.fromFullyApplied fullyAppliedRelExpr with
  | .success equivRel => return equivRel
  | .missingArgs numArgs =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a binary relation, but takes {numArgs} arguments."
  | .illformedType type =>
    throwError "The type of {indentExpr fullyAppliedRelExpr}\nis not compatible with `quotify`. It \
                is expected to be a homogeneous binary relation, but is {indentExpr type}"


elab "#quotify_setoid " rel:term : command =>
  withRef rel <| liftTermElabM do
    let equivRel ← elabEquivRel rel
    let some inst ← equivRel.getSetoid? | throwError "No setoid found for {indentExpr equivRel}"
    logInfo inst

elab "#quotify_rel " rel:term : command =>
  withRef rel <| liftTermElabM do
    let equivRel ← elabEquivRel rel
    withOptions (·.setBool `pp.fieldNotation.generalized false) do
      logInfo equivRel

/--
Show all `quotify` theorems registered for a given relation. If not relation is provided, all
registered theorems for all relations are shown.
-/
elab "#quotify_theorems " rel?:(term)? : command => do
  let thms := extension.getState (← getEnv)
  if let some rel := rel? then
    withRef rel <| liftTermElabM do
      let equivRel ← elabEquivRel rel
      let some thms := thms[equivRel]?
        | throwError "No `quotify` theorems have been registered for {indentExpr equivRel}"
      let msg : MessageData := thms.map MessageData.ofConstName
      logInfo msg
  else
    for (equivRel, thms) in thms do
      let thmsMsg : MessageData := thms.map MessageData.ofConstName
      logInfo m!"{equivRel}:\n{thmsMsg}"

end Quotify
