import Quotify.Command

@[quotify]
def s₂ : Setoid (List Nat) where
  r := List.Perm
  iseqv := sorry

/-- info: ❌ -/
#guard_msgs in
#quotify_equiv List.Perm

/-- info: ✅ -/
#guard_msgs in
#quotify_equiv @List.Perm Nat

attribute [-quotify] s₂

/-- info: ❌ -/
#guard_msgs in
#quotify_equiv List.Perm

/-- info: ❌ -/
#guard_msgs in
#quotify_equiv @List.Perm Nat

@[quotify]
def s₁ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry

/-- info: ✅ -/
#guard_msgs in
#quotify_equiv List.Perm

/-- info: ✅ -/
#guard_msgs in
#quotify_equiv @List.Perm Nat
