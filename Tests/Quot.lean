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

/--
info: fun lhs rhs => Quotient.mk { r := List.Perm, iseqv := ⋯ } lhs = Quotient.mk { r := List.Perm, iseqv := ⋯ } rhs
-/
#guard_msgs in
#quotify_quot @List.Perm Nat

/- **TODO** Look into the level parameter name mismatch of the `BinRel` and the equivalence proof.

fun (x_0 : Type _uvar.0) (lhs rhs : List.{_uvar.0} x_0) =>
  @Eq.{_uvar.0 + 1}
    (@Quotient.{_uvar.0 + 1} (List.{_uvar.0} x_0)
      (@Setoid.mk.{_uvar.0 + 1} (List.{_uvar.0} x_0) (@List.Perm.{_uvar.0} x_0)
        (@Setoid.iseqv.{u_1 + 1} (List.{u_1} x_0)
          ((fun (α : Type u_1) =>
              (fun (α : Type u_1) => @Setoid.mk.{u_1 + 1} (List.{u_1} α) (@List.Perm.{u_1} α) (List.Perm.eqv.{u_1} α))
                α)
            x_0))))
    (@Quotient.mk.{_uvar.0 + 1} (List.{_uvar.0} x_0)
      (@Setoid.mk.{_uvar.0 + 1} (List.{_uvar.0} x_0) (@List.Perm.{_uvar.0} x_0)
        (@Setoid.iseqv.{u_1 + 1} (List.{u_1} x_0)
          ((fun (α : Type u_1) =>
              (fun (α : Type u_1) => @Setoid.mk.{u_1 + 1} (List.{u_1} α) (@List.Perm.{u_1} α) (List.Perm.eqv.{u_1} α))
                α)
            x_0)))
      lhs)
    (@Quotient.mk.{_uvar.0 + 1} (List.{_uvar.0} x_0)
      (@Setoid.mk.{_uvar.0 + 1} (List.{_uvar.0} x_0) (@List.Perm.{_uvar.0} x_0)
        (@Setoid.iseqv.{u_1 + 1} (List.{u_1} x_0)
          ((fun (α : Type u_1) =>
              (fun (α : Type u_1) => @Setoid.mk.{u_1 + 1} (List.{u_1} α) (@List.Perm.{u_1} α) (List.Perm.eqv.{u_1} α))
                α)
            x_0)))
      rhs)
-/
