def Option.casesOn' : Option α → β → (α → β) → β
  | none, n, _ => n
  | some a, _, s => s a

protected def Quot.map (f : α → β) (h : ∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) : Quot ra → Quot rb :=
  Quot.lift (fun x => Quot.mk rb (f x)) fun _ _ hra ↦ Quot.sound <| h hra

namespace Quotient

notation:arg "⟦" a "⟧" => Quotient.mk _ a

variable {sa : Setoid α} {sb : Setoid β} {sc : Setoid γ}

protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) : Quotient sa → Quotient sb :=
  Quot.map f h

protected def map₂ (f : α → β → γ) (h : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄, b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y => .mk _ (f x y)) fun _ _ _ _ h₁ h₂ => Quot.sound <| h h₁ h₂

@[simp]
theorem lift_mk (f : α → β) (h) (x : α) : Quotient.lift f h (.mk s x) = f x :=
  rfl

@[simp]
theorem lift₂_mk (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h (.mk _ a) (.mk _ b) = f a b :=
  rfl

@[simp]
theorem map_mk (f : α → β) (h) (x : α) : Quotient.map f h (.mk sa x) = .mk sb (f x) :=
  rfl

@[simp]
theorem map₂_mk (f : α → β → γ) (h) (x : α) (y : β) :
    Quotient.map₂ f h (.mk sa x) (.mk sb y) = .mk sc (f x y) :=
  rfl

end Quotient
