-- import Quotify.Signature
-- import Quotify.Translate
-- import Quotify.Attribute
import Quotify.Unexpanders
/-
From:
  https://github.com/FWuermse/grw/blob/main/GrwTest/SetEq.lean
-/

def setEq {α : Type} : List α → List α → Prop :=
  fun l1 l2 => ∀ x, x ∈ l1 <-> x ∈ l2

instance setEqEquivalence {α : Type} : Equivalence (@setEq α) where
  refl := fun l1 x => Iff.rfl
  symm := by
    intro x y hxy
    unfold setEq
    intro a
    apply Iff.symm
    exact hxy a
  trans := by
    intro x y z hxy hyz
    unfold setEq at *
    intro a
    apply Iff.intro
    intro hx
    rw [hxy a] at hx
    rw [hyz a] at hx
    assumption
    intro hy
    rw [← hyz a] at hy
    rw [← hxy a] at hy
    assumption

instance Setoid_List {α : Type} : Setoid (@List α) where
  r     := fun l1 l2 => ∀ x, x ∈ l1 <-> x ∈ l2
  iseqv := setEqEquivalence

def addElem {α : Type} (x : α) (l : List α) : List α :=
  x :: l



theorem addElem_sig (x : α) : ∀ (a₁ a₂ : List α), a₁ ≈ a₂ → addElem x a₁ ≈ addElem x a₂ := by
  intro a₁ a₂ heq x
  simp [addElem]
  constructor
  · intro hx
    cases hx with
    | inl => left; assumption
    | inr h' =>
      right; exact (heq x).mp h'
  · intro hx
    cases hx with
    | inl => left; assumption
    | inr h' => right; exact (heq x).mpr h'

theorem rewriteExample (h : setEq [1,2,3] [3,2,1]) : setEq (addElem 4 [1,2,3]) (addElem 4 [3,2,1]) := by
  have e : @setEq Nat = (fun lhs rhs => Quotient.mk Setoid_List lhs = Quotient.mk Setoid_List rhs) := sorry
  revert h
  simp only [e]
  intro h
  clear e
  simp only [← Quotient.map_mk _ (addElem_sig _) _]
  -- --
  rw [h]
