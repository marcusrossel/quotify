import Quotify.Tactic
import Quotify.Command
-- import Quotify.Unexpanders

@[quotify]
theorem t (l₁ l₂ : List α) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

attribute [quotify] List.isSetoid

example (l₁ l₂ : List α) (h : l₁.reverse ≈ l₂.reverse) : l₁ ≈ l₂ := by
  quotify
  -- **TODO** I think the problem is that the setoid is not being matched. Can we avoid this by
  --          using the original setoid matched for the relation when constructing the
  --          iffQuotientEq theorem?
  --
  --          More generally, the `Quotient.*` theorems rewrite the compatability theorems to be
  --          stated specifically in terms of `≈`. So if we change the `≈` in `t` to `List.Perm`, we
  --          get an application mismatch when constructing the term `Quotient.map_mk ...` below.
  --          Should we require `≈` in `quotify` theorems too, or just construct an equivalent
  --          theorem that uses `≈` on the fly, when necessary?

  simp only [← @Quotient.map_mk _ _ _ _ _ (@t _)] at h
  rw [← Quotient.map_mk _ t] at h
  erw [← Quotient.map_mk _ t] at h
