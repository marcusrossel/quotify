import Quotify.Command

@[quotify]
def s₁ : Setoid (List Nat) where
  r := List.Perm
  iseqv := sorry

/--
error: The relation ⏎
  fun x_0 => List.Perm
has no matching `Setoid` marked with `[quotify]`.
-/
#guard_msgs in
#quotify_setoid List.Perm

/-- info: s₁ -/
#guard_msgs in
#quotify_setoid @List.Perm Nat

attribute [-quotify] s₁

/--
error: The relation ⏎
  fun x_0 => List.Perm
has no matching `Setoid` marked with `[quotify]`.
-/
#guard_msgs in
#quotify_setoid List.Perm

/--
error: The relation ⏎
  List.Perm
has no matching `Setoid` marked with `[quotify]`.
-/
#guard_msgs in
#quotify_setoid @List.Perm Nat

@[quotify]
def s₂ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry

/-- info: s₂ -/
#guard_msgs in
#quotify_setoid List.Perm

/-- info: s₂ -/
#guard_msgs in
#quotify_setoid @List.Perm Nat
