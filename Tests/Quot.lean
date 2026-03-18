import Quotify.Command

attribute [quotify] List.isSetoid

/--
info: ∀ (x_0 : Type _uvar.0) (lhs rhs : List x_0),
  lhs.Perm rhs ↔ Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot List.Perm

/--
info: ∀ (α : Type _uvar.0) (lhs rhs : List α),
  lhs.Perm rhs ↔ Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot ((· ≈ ·) : List ?α → List ?α → Prop)

/--
info: ∀ (lhs rhs : List Nat),
  lhs.Perm rhs ↔ Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot @List.Perm Nat
