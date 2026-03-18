import Quotify.Command

@[quotify]
theorem t₁ : [].Perm (α := α) [] := by rfl

@[quotify]
theorem t₂ (l₁ l₂ : List α) : l₁ ≈ l₂ := sorry

@[quotify]
theorem t₃ (l₁ l₂ : List α) : (List.isSetoid _).r l₁ l₂ := sorry

/-- info: [t₁, t₂, t₃] -/
#guard_msgs in
#quotify_theorems List.Perm

namespace X

opaque t₁ : Nat

/-- info: [_root_.t₁, t₂, t₃] -/
#guard_msgs in
#quotify_theorems List.Perm

end X

/-- info: [t₁, t₂, t₃] -/
#guard_msgs in
#quotify_theorems @List.Perm Nat

@[quotify]
theorem t₄ (l₁ l₂ : List Nat) : l₁ ≈ l₂ := sorry

/-- info: [t₁, t₂, t₃] -/
#guard_msgs in
#quotify_theorems List.Perm

/-- info: [t₁, t₂, t₃, t₄] -/
#guard_msgs in
#quotify_theorems @List.Perm Nat

/--
info: fun α => @List.Perm α:
[t₁, t₂, t₃]
---
info: @List.Perm Nat:
[t₄]
-/
#guard_msgs in
set_option pp.explicit true in
#quotify_theorems
