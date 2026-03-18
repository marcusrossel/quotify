import Quotify.Tactic
import Quotify.Unexpanders

attribute [quotify] List.isSetoid

/--
error: unsolved goals
l₁ l₂ : List Nat
h : ⟦l₁.reverse⟧ = ⟦l₂.reverse⟧
⊢ ⟦l₁⟧ = ⟦l₂⟧
-/
#guard_msgs in
example (l₁ l₂ : List Nat) (h : l₁.reverse.Perm l₂.reverse) : l₁.Perm l₂ := by
  quotify

-- **BUG** Running in a reverted context produces dangling fvars.
set_option pp.explicit true in
example (l₁ l₂ : List α) (h : l₁.reverse.Perm l₂.reverse) : l₁.Perm l₂ := by
  quotify

example (l₁ l₂ : List Nat) : l₁ ≈ l₂ := by
  quotify
