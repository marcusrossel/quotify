import Quotify.Translate
import Mathlib.Tactic

def R : Nat → relation Nat := fun n x y => x.mod n = y.mod n

-- Setoid instance here:
instance R_Setoid (n : Nat) : Setoid Nat :=
  { r := R n
    iseqv :=
      { refl :=
          by
          unfold R
          aesop
        symm :=
          by
          unfold R
          aesop
        trans :=
          by
          unfold R
          aesop
                }
                  }


def add_sig : (n : Nat) → Signature (Nat.add) ((R n) ⟹ (R n) ⟹ (R n)) :=
  by
  sorry


def mul_sig :  (n : Nat) → Signature (Nat.mul) ((R n) ⟹ (R n) ⟹ (R n)) :=
  by sorry


example (x_R_y : R n x y) : R n (3 * (1 + (7 + x) + 5)) ((1 + 7 + y + 5) * 3)   :=
  by
  simp_rw [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul] at *

  translateF R R_Setoid
    [⟨Nat.add, add_sig⟩,
     ⟨Nat.mul, mul_sig⟩]
  rw [x_R_y]
  translateB R R_Setoid
    [⟨Nat.add, add_sig⟩,
     ⟨Nat.mul, mul_sig⟩]

  suffices eq : (Nat.mul 3 ((Nat.add 1 (Nat.add 7 y)).add 5)) = ((((Nat.add 1 7).add y).add 5).mul 3)
    by
    rewrite [eq] ; clear eq
    aesop
  grind
