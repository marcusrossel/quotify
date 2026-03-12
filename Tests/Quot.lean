import Quotify.Command

attribute [quotify] List.isSetoid

/--
info: fun x_0 lhs rhs => Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot List.Perm

/--
info: fun α lhs rhs => Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot ((· ≈ ·) : List ?α → List ?α → Prop)

-- TODO
#quotify_quot @List.Perm Nat
