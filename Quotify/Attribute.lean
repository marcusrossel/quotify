module
public import Lean.Meta.Basic
public import Quotify.EquivRel

open Lean Meta Std

namespace Quotify.Extension

public abbrev Theorem  := Name
public abbrev Theorems := HashMap EquivRel (List Theorem)

public structure Entry where
  key : EquivRel
  val : Theorem
  deriving Inhabited

def Theorems.addEntry (thms : Theorems) (entry : Entry) : Theorems :=
  thms.alter entry.key fun
    | some thms => thms.concat entry.val
    | none      => [entry.val]

end Extension

open Extension

public abbrev Extension := SimpleScopedEnvExtension Entry Theorems

def Extension.mk : IO Extension :=
  registerSimpleScopedEnvExtension {
    initial := ∅
    addEntry := Theorems.addEntry
  }

public initialize extension : Extension ← Extension.mk

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
