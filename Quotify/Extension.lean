module
public import Lean.Meta.Basic
public import Quotify.EquivRel

open Lean Std

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
