import Quotify.Translate

def R : Nat → Nat → Nat → Prop := fun n x y => x.mod n = y.mod n

-- Setoid instance here:
instance R_Setoid (n : Nat) : Setoid Nat where
  r := R n
  iseqv := sorry

/-
def add_sig : (n : Nat) → Signature (Nat.add) ((R n) ⟹ (R n) ⟹ (R n)) :=
  by
  sorry


def mul_sig :  (n : Nat) → Signature (Nat.mul) ((R n) ⟹ (R n) ⟹ (R n)) :=
  by sorry
-/

example (x_R_y : R n x y) : R n (3 * (1 + (7 + x) + 5)) ((1 + 7 + y + 5) * 3) := by
  -- TODO: The setoid approach already does not make sense here. Over which type is the setoid?
  --       `Nat`?
  translateF
    [⟨Nat.add, add_sig⟩,
     ⟨Nat.mul, mul_sig⟩]
  rw [x_R_y]
  translateB
    [⟨Nat.add, add_sig⟩,
     ⟨Nat.mul, mul_sig⟩]

  suffices eq : (Nat.mul 3 ((Nat.add 1 (Nat.add 7 y)).add 5)) = ((((Nat.add 1 7).add y).add 5).mul 3)
    by
    rewrite [eq] ; clear eq
    sorry
  grind
