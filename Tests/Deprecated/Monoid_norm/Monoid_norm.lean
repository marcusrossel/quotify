import Quotify.Translate
-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α


inductive R : (Exp α) → (Exp α) → Prop
| assoc {e e' e'' : Exp α} : R ((e.app e').app e'') (e.app (e'.app e''))
| id_left {e  : Exp α}     : R ((Exp.id).app e) (e)
| id_right {e : Exp α}     : R (e.app Exp.id) (e)
| refl     {e : Exp α}     : R (e) (e)
| symm      {e e' : Exp α}  : R (e) (e') → R (e') (e)
| trans {e e' e'' : Exp α} : R (e) (e') → R (e') (e'') → R (e) (e'')
| app {a b c d : Exp α}    : R (a) (b) → R (c) (d) → R (a.app c) (b.app d)


def eval : (Exp α) → (Exp α → Exp α)
  | Exp.app a b => (λ e => eval a (eval b e))
  | Exp.id      => id
  | Exp.elem x  => (λ e => (Exp.elem x).app e)

-- ∀ b, a.app b ~ [[a]]b
theorem eval_lemma1 (a : Exp α) : ∀ b, R (a.app b) ((eval a) b) := by
  induction a
  case app c d c_ih d_ih =>
    intro b
    specialize d_ih b
    specialize c_ih (eval d b)
    -- R-rewriting here
    have h0 : R ((c.app d).app b) (c.app (d.app b)) := R.assoc
    refine (R.trans h0 ?_)
    clear h0
    have h0 : R (c.app (d.app b)) (c.app (eval d b)) := R.app (R.refl) (d_ih)
    refine (R.trans h0 ?_)
    clear h0
    exact c_ih

  case id =>
    intro b
    exact R.id_left

  case elem =>
    intro b
    exact R.refl

-- a ~ b  → ∀ c, [[a]]c = [[b]]c
theorem eval_lemma2 {a b : Exp α} (h : R a b) : ∀ c : Exp α, (eval a) c = (eval b) c := by
  induction h

  any_goals
    intros; grind

  case app a b c d _ _ ab_ih cd_ih =>
    -- clear  - ab_ih cd_ih
    intro e
    specialize cd_ih e
    specialize ab_ih ((eval d) e)
    simp only [eval]
    rw [cd_ih]
    rw [ab_ih]
  all_goals sorry


def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id

def nbe (e : Exp α) : Exp α := reify (eval e)

-- Shows decidability of e ~ e'
theorem correctness (e e' : Exp α) : (R (e) (e')) ↔ (nbe e = nbe e') := by
  apply Iff.intro
  · intro h
    induction h
    any_goals
      aesop
    case mp.app a b c d a_r_b c_r_d _ _ =>
      clear * - a_r_b c_r_d
      apply eval_lemma2 ?_ Exp.id
      -- R-rewriting here
      exact R.app a_r_b c_r_d

  · unfold nbe reify
    intro h0
    -- R-rewriting here
    have h1 : R (e) (e.app Exp.id) := (R.symm R.id_right)
    refine (R.trans h1 ?_)
    clear h1
    have h1 : R (e.app Exp.id) ((eval e) Exp.id) := eval_lemma1 e Exp.id
    refine (R.trans h1 ?_)
    clear h1
    rewrite [h0]
    clear h0
    have h0 : R ((eval e') Exp.id) (e'.app Exp.id) := R.symm (eval_lemma1 e' Exp.id)
    refine (R.trans h0 ?_)
    clear h0
    exact R.id_right




-- ((1, 2), ((0, 0), 3)) ~ ((0, 0), (1, (2, (0, 3))))
def zero := (Exp.id : Exp Nat)
def one  := Exp.elem 1
def two  := Exp.elem 2
def three := Exp.elem 3
example : R
          ( (one.app two).app  ((zero.app zero).app three) )
          ( (zero.app zero).app (one.app (two.app (zero.app three)))) :=
  by
  have h0 : R (zero.app zero)  zero := R.id_left
  have h1 : R ((zero.app zero).app three) (zero.app three) := R.app h0 R.refl
-- ((1, 2), ((0, 0), 3)) ~ ((1, 2), (0, 3))
  have h2 : R ((one.app two).app ((zero.app zero).app three))
                  ((one.app two).app (zero.app three)) := R.app R.refl h1
-- ((1, 2), (0, 3)) ~ (1, (2, (0, 3))
  have h3 : R ((one.app two).app (zero.app three))
                  (one.app (two.app (zero.app three))) := R.assoc
  have h4 : R zero (zero.app zero) := R.symm h0
-- (1, (2, (0, 3)) ~ (0, (1, (2, (0, 3)))
  have h5 : R (one.app (two.app (zero.app three)))
                  (zero.app (one.app (two.app (zero.app three)))) := R.symm R.id_left
-- (0, (1, (2, (0, 3))) ~ ((0, 0), (1, (2, (0, 3)))
  have h6 : R (zero.app (one.app (two.app (zero.app three))))
                  ((zero.app zero).app (one.app (two.app (zero.app three)))) := R.app h4 R.refl
  clear h0 h1 h4
  apply R.trans h2
  apply R.trans h3
  apply R.trans h5
  apply R.trans h6
  exact R.refl
