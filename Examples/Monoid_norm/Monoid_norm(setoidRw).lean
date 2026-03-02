import Quotify.Translate
import Mathlib.Tactic

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α


inductive R : {α : Type} → relation (Exp α)
| assoc {e e' e'' : Exp α} : R ((e.app e').app e'') (e.app (e'.app e''))
| id_left {e  : Exp α}     : R ((Exp.id).app e) (e)
| id_right {e : Exp α}     : R (e.app Exp.id) (e)
| refl     {e : Exp α}     : R (e) (e)
| symm      {e e' : Exp α}  : R (e) (e') → R (e') (e)
| trans {e e' e'' : Exp α} : R  (e) (e') → R (e') (e'') → R (e) (e'')
| app {a b c d : Exp α}    : R (a) (b) → R (c) (d) → R (a.app c) (b.app d)


-- Setoid instance here:
instance R_Setoid : Setoid (Exp α) :=
  { r := @R α
    iseqv :=
      { refl := λ _ => R.refl
        symm := R.symm
        trans := R.trans
      }
  }

def app_sig (α : Type) : Signature (@Exp.app α) (R ⟹ R ⟹ R )
  :=
  by
  simp only [Signature, respectful]
  exact fun x y a x_2 y_2 a_1 => R.app a a_1


def eval : (Exp α) → (Exp α → Exp α)
  | Exp.app a b => (λ e => eval a (eval b e))
  | Exp.id      => id
  | Exp.elem x  => (λ e => (Exp.elem x).app e)


-- ∀ b, a.app b ~ [[a]]b
lemma eval_lemma1 {α : Type} (a : Exp α) : ∀ b, R (a.app b) ((eval a) b) :=
by
  induction a

  case app c d c_ih d_ih =>
    unfold eval
    intro b
    specialize d_ih b
    specialize c_ih (eval d b)

    have R.assoc := @R.assoc
    translateF R R_Setoid [⟨Exp.app, app_sig⟩]
    -- (c ⬝ d) ⬝ b ~ c ⬝ (d ⬝ b) ~ c ⬝ (eval d b) ~ eval c (eval d b)
    rw [R.assoc, d_ih, c_ih]

  case id =>
    intro b
    exact R.id_left

  case elem =>
    intro b
    exact R.refl


lemma eval_sig : (α : Type) → Signature (@eval α) (R ⟹ Eq) :=
by
  intro α a b h
  apply funext
  induction h

  any_goals
    intros; aesop

  case app a b c d _ _ ab_ih cd_ih =>
    clear * - ab_ih cd_ih
    intro e
    specialize cd_ih e
    specialize ab_ih ((eval d) e)
    simp only [eval]
    rw [cd_ih, ab_ih]


def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id

def nbe (e : Exp α) : Exp α := reify (eval e)

-- Shows decidability of e ~ e'
theorem correctness (e e' : Exp α) : (R (e) (e')) ↔ (nbe e = nbe e') :=
by
  apply Iff.intro
  · intro h
    induction h
    any_goals
      aesop
    case mp.app a b c d a_r_b c_r_d _ _ =>
      clear * - a_r_b c_r_d
      unfold nbe reify
      translateF R R_Setoid
                [⟨Exp.app, app_sig⟩,
                 ⟨eval, eval_sig⟩]
      grind

  · unfold nbe reify
    intro h0
    -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
    have R.id_right := @R.id_right
    have eval_lemma1:= @eval_lemma1
    translateF R R_Setoid []
    -- e ~ e ⬝ id ~ nbe e = nbe e' ~ e' ⬝ id ~ e'
    rw [← R.id_right, eval_lemma1 e Exp.id, h0,
                    ← eval_lemma1 e' Exp.id, R.id_right]
