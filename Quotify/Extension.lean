module
public import Lean.Meta.Basic

open Lean Std

namespace Quotify.Extension

/- Note:
Currently, we only save the *name* of a setoid instance. This does not necessarily denote a unique
instance, as the instance may be polymorphic. For example, `List.isSetoid` denotes all instances of
the form `Setoid (List α)`.
Saving the setoid instance instead of the underlying equivalence relation has the benefit that the
equivalence relation may not have a named declaration of its own. For example, `List.isSetoid`'s
underlying equivalence relation is `List.Perm`, which has a named declaraion. However, we could also
define the equivalence relation inline in the setoid instance, in which case there would not be a
simple name to associate with the equivalence relation.
-/
public abbrev Setoid := Name

public abbrev Theorem := Name
public abbrev Theorems := HashMap Setoid (List Theorem)

public structure Entry where
  key : Setoid
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
