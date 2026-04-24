import Quotify.Tactic
import Quotify.Command
import Quotify.Unexpanders

@[quotify]
theorem t (l₁ l₂ : List α) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

attribute [quotify] List.isSetoid

/--
error: unsolved goals
α : Type u_1
l₁ l₂ : List α
h : (⟦List.reverse⟧) ⟦l₁⟧ = (⟦List.reverse⟧) ⟦l₂⟧
⊢ ⟦l₁⟧ = ⟦l₂⟧
-/
#guard_msgs in
example (l₁ l₂ : List α) (h : l₁.reverse ≈ l₂.reverse) : l₁ ≈ l₂ := by
  quotify
