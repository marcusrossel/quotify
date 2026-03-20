import Quotify.Command

/--
error: Theorems marked with `[quotify]` must have one of the following forms:

• `∀ …, ∀ a b, (a ≈ b) → f a = f b`
• `∀ …, ∀ a₁ b₁ a₂ b₂, (a₁ ≈ a₂) → (b₁ ≈ b₂) → f a₁ b₁ = f a₂ b₂`
• `∀ …, ∀ a b, (a ≈ b) → f a ≈ f b`
• `∀ …, ∀ a₁ a₂, (a₁ ≈ a₂) → ∀ b₁ b₂, (b₁ ≈ b₂) → f a₁ b₁ ≈ f a₂ b₂`

The given theorem does not match any of these.
-/
#guard_msgs(error) in
@[quotify]
theorem t₁ (l₁ l₂ : List α) : l₁ ≈ l₂ := sorry

@[quotify]
theorem t₂ (l₁ l₂ : List α) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

@[quotify]
theorem t₃ (l₁ l₂ : List α) (h : (List.isSetoid _).r l₁ l₂) : l₁.reverse ≈ l₂.reverse := sorry

/-- info:
• map: [t₂, t₃]
-/
#guard_msgs in
#quotify_theorems List.Perm

namespace X

opaque t₂ : Nat

/-- info:
• map: [_root_.t₂, t₃]
-/
#guard_msgs in
#quotify_theorems List.Perm

end X

/-- info:
• map: [t₂, t₃]
-/
#guard_msgs in
#quotify_theorems @List.Perm Nat

@[quotify]
theorem t₄ (l₁ l₂ : List Nat) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

/-- info:
• map: [t₂, t₃]
-/
#guard_msgs in
#quotify_theorems List.Perm

/-- info:
• map: [t₂, t₃, t₄]
-/
#guard_msgs in
#quotify_theorems @List.Perm Nat

/--
info:
fun α => @List.Perm α:
  • map: [t₂, t₃]
  ⏎
@List.Perm Nat:
  • map: [t₄]
-/
#guard_msgs in
set_option pp.explicit true in
#quotify_theorems

-- **TODO** Add some flexibility to the order in which arguments of `quotify` theorems can be given.
@[quotify]
theorem t₅ (l₁ l₂ r₁ r₂ : List α) (h₁ : l₁ ≈ l₂) (h₂ : r₁ ≈ r₂) : l₁ ++ r₁ ≈ l₂ ++ r₂ := sorry

@[quotify]
theorem t₆ (l₁ l₂ : List α) (h₁ : l₁ ≈ l₂) (r₁ r₂ : List α) (h₂ : r₁ ≈ r₂) : l₁ ++ r₁ ≈ l₂ ++ r₂ := sorry

/--
info:
• map: [t₂, t₃]
• map₂: [t₆]
-/
#guard_msgs in
#quotify_theorems List.Perm
