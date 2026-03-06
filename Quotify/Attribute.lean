module
public import Lean.Meta.Basic
public import Quotify.BinRel
public import Quotify.Setoid

open Lean Meta Std

namespace Quotify.Extension

public abbrev Theorem  := Name
public abbrev Theorems := HashMap BinRel (List Theorem)
public abbrev Setoids  := HashMap BinRel Setoid

-- TODO: If the key-types stay the same, you can collapse `Theorems` and `Setoids` into a single
--       hashmap.
public structure Info where
  theorems : Theorems
  setoids  : Setoids
  deriving Inhabited

instance : EmptyCollection Info where
  emptyCollection := { theorems := ∅, setoids := ∅ }

public inductive Entry.Val where
  | theorem (val : Theorem)
  | setoid (val : Setoid)
  deriving Inhabited

public structure Entry where
  key : BinRel
  val : Entry.Val
  deriving Inhabited

def Theorems.add (thms : Theorems) (key : BinRel) (thm : Theorem) : Theorems :=
  thms.alter key fun
    | some thms => thms.concat thm
    | none      => [thm]

def Info.addEntry (info : Info) (entry : Entry) : Info :=
  match entry.val with
  | .theorem thm => { info with theorems := info.theorems.add entry.key thm }
  | .setoid _ => info -- TODO

end Extension

open Extension

public abbrev Extension := SimpleScopedEnvExtension Entry Info

def Extension.mk : IO Extension :=
  registerSimpleScopedEnvExtension {
    initial  := ∅
    addEntry := Info.addEntry
  }

public initialize extension : Extension ← Extension.mk

def binRelForThm (thmInfo : TheoremVal) : MetaM BinRel := do
  let thmType := thmInfo.type
  let (_, _, fullyAppliedThmType) ← forallMetaTelescopeReducing thmType
  let .success binRel ← BinRel.fromFullyApplied fullyAppliedThmType
    | throwError "You can only use the `[quotify]` attribute on theorems of the form \
                  `∀ … lhs rhs, r … lhs rhs` where `r …` is a homogeneous binary relation."
  return binRel

inductive Target where
  | theorem (binRel : BinRel)
  | setoid -- TODO

def Target.forDecl (declName : Name) : MetaM Target := do
  match ← getConstInfo declName with
  | .thmInfo thmInfo =>
    let binRel ← binRelForThm thmInfo
    return .theorem binRel
  | .defnInfo _defInfo =>
    return .setoid -- TODO
  | _ => throwError "You can only use the `[quotify]` attribute on theorems or definitions, but \
                     `{.ofConstName declName}` is neither."

def addQuotifyAttribute (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  recordExtraModUseFromDecl (isMeta := false) declName
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  match ← Target.forDecl resolvedDeclName with
  | .theorem binRel => extension.add { key := binRel, val := .theorem resolvedDeclName } attrKind
  | .setoid         => return -- TODO

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name := `quotify
    descr := "The `[quotify]` attribute is used to annotate `Setoid`s of equivalence relations for \
              for use with the `quotify` tactic, as well as theorems which prove compatability of \
              given functions with those equivalence relations."
    applicationTime := .afterCompilation
    add declName stx attrKind := MetaM.run' <| withRef stx <| addQuotifyAttribute declName attrKind
  }
