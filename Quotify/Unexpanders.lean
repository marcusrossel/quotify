import Quotify.Mathlib

@[app_unexpander Quotient.mk]
def unexpandMk : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $t:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.lift]
def unexpandLift : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.lift₂]
def unexpandLift₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.map]
def unexpandMap : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.map₂]
def unexpandMap₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()
