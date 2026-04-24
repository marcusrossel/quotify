import Quotify.Command

@[quotify]
theorem t (l₁ l₂ : List α) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

@[quotify]
theorem s (l₁ l₂ : List Nat) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

attribute [quotify] List.isSetoid

/--
info:
t: fun {x} => Eq.symm (Quotient.map_mk List.reverse t x)
s: fun {x} => Eq.symm (Quotient.map_mk List.reverse s x)
-/
#guard_msgs in
#quotify_push @List.Perm Nat

/-- info: t: fun x_0 {x} => Eq.symm (Quotient.map_mk List.reverse t x) -/
#guard_msgs in
#quotify_push List.Perm
