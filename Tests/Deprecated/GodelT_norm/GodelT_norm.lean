import Mathlib.Tactic

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Ty : Type
| nat : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow

inductive Exp : Ty → Type
| K {a b : Ty}     :  Exp (a ⇒' b ⇒' a)
| S {a b c : Ty}   :  Exp ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))
| app {a b : Ty}   :  Exp (a ⇒' b) → Exp a → Exp b
| zero             :  Exp nat
| succ             :  Exp (nat ⇒' nat)
| recN {a : Ty}    :  Exp (a ⇒' (nat ⇒' a ⇒' a) ⇒' nat ⇒' a)
open Exp
infixl : 100 " ⬝ " => app

-- Didn't declare Setoid instance yet
inductive R : Π {α : Ty}, (Exp α) → (Exp α) → Prop
| refl {α : Ty}{e : Exp α}
        : R (e) (e)
| symm   {α : Ty}{e e' : Exp α}
        : R (e) (e') → R (e') (e)
| trans {α : Ty}{e e' e'' : Exp α}
        : R (e) (e') → R (e') (e'') → R (e) (e'')
| K     {α β : Ty}{x : Exp α} {y : Exp β}
        : R (K ⬝ x ⬝ y) (x)
| S     {α β γ: Ty}{x : Exp (γ ⇒' β ⇒' α)} {y : Exp (γ ⇒' β)} {z : Exp γ}
        : R (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app   {α β : Ty} {a b : Exp (β ⇒' α)} {c d : Exp β}
        : R (a) (b) → R (c) (d) → R (a ⬝ c) (b ⬝ d)
| recN_zero {α : Ty} {e : Exp α} {f : Exp (nat ⇒' α ⇒' α)}
        : R (recN ⬝ e ⬝ f ⬝ zero) (e)
| recN_succ {α : Ty} {n : Exp nat} {e : Exp α} {f : Exp (nat ⇒' α ⇒' α)}
        : R (recN ⬝ e ⬝ f ⬝ (succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))


def Ty_inter : Ty → Type
| nat => ℕ

| arrow a b => Exp (a ⇒' b) × (Ty_inter a → Ty_inter b)


def numeral : ℕ → Exp nat
| 0 => zero

| n+1 => succ ⬝ (numeral n)


def reify (α : Ty) (e : Ty_inter α) : Exp α :=
  match α,e with
  | nat, e            => numeral e

  | Ty.arrow α β, (c, f) => c


def appsem {a b : Ty} (t : Ty_inter (a ⇒' b)) (e' : Ty_inter a) : Ty_inter b := (t.snd e')


def Exp_inter (a : Ty) : (e : Exp a) → Ty_inter a
| @K a b => (K,
            (λ p ↦ (K ⬝ (reify a p),
            (λ _ ↦ p))))
| @S a b c => (S,
              (λ x ↦ (S ⬝ (reify (a⇒'b⇒'c) x),
              (λ y ↦ (S ⬝ (reify (a⇒'b⇒'c) x) ⬝ (reify (a⇒'b) y),
              (λ z ↦ appsem (appsem x z) (appsem y z)))))))
| @app a b f e  => appsem (Exp_inter (a ⇒' b) f) (Exp_inter a e)
| zero          => (0 : ℕ)
| succ          => (succ,
                   (λ n : ℕ ↦ n+1) )
| @recN a       => (recN,
                   (λ p ↦ (recN ⬝ (reify a p),
                   (λ q ↦ (recN ⬝ (reify a p) ⬝ (reify (nat⇒'a⇒'a) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))


def nbe (a : Ty) (e : Exp a) : (Exp a) := reify a (Exp_inter a e)


-- e ~ e'  implies [[e]]a = [[e']]a
lemma R_lemma1 {a : Ty} {e e' : Exp a} : R e e' → ((Exp_inter a e) = (Exp_inter a e')) :=
by
  intro h
  induction h
  any_goals aesop
  case app α β a b c d a_r_b c_r_d ab_ih cd_ih =>
    unfold Exp_inter
    rw [ab_ih, cd_ih]

-- e ~ e'  implies nbe a e = nbe a e'
lemma soundness {a : Ty} {e e' : Exp a} : R e e' → nbe a e = nbe a e' :=
by
  unfold nbe
  intro h1
  have h2 : Exp_inter a e = Exp_inter a e' := R_lemma1 h1
  rw [h2]


-- Tait-reducibility relation
def Red : (a : Ty) → (e : Exp a) → Prop
| nat, e       => R e (nbe nat e)

| arrow α β, e => R e (nbe (α ⇒' β) e)  ∧  ∀ e', Red α e' → Red β (app e e')

-- R a e  implies  e ~ nbe a e
lemma Red_R_nbe (h : Red a e)  : R e (nbe a e) :=
  by
  cases a
  all_goals (unfold Red at h); aesop

-- e ~ e' implies  R α e ↔ R α e'
lemma Red_resp : ∀ e e', R e e' → (Red α e = Red α e') :=
  by
  refine fun e e' a ↦ ?_ ; apply propext ; revert a e' e
  induction α
  · unfold Red
    intro a b a_r_b
    apply Iff.intro
    · intro a_r_nbe
      --R-rewriting here:
      -- b ~ a ~ nbe a = nbe b
      -- "rewrite [← a_r_b, a_r_nbe, soundness a_r_b]"
      have eq : nbe nat a = nbe nat b := soundness a_r_b
      (rewrite [← eq]); clear eq
      apply R.trans (a_r_b).symm
      exact a_r_nbe
    · intro b_r_nbe
      --R-rewriting here:
      -- a ~ b ~ nbe b = nbe a
      -- "rewrite [a_r_b, b_r_nbe, ← soundness a_r_b]"
      have eq : nbe nat a = nbe nat b := soundness a_r_b
      (rewrite [eq]); clear eq
      exact R.trans a_r_b b_r_nbe

  · rename_i α β _ βIH
    intros f1 f2 f1_r_f2
    apply Iff.intro
    · intro R_f1
      apply And.intro
      · have f1_r_nbe := Red_R_nbe R_f1; clear R_f1
        -- R-rewriting here:
        -- f2 ~ f1 ~ nbe f1 = nbe f2
        -- "rewrite [← f1_r_f2, f1_r_nbe, soundness f1_r_f2]"
        have eq : nbe (α ⇒' β) f1 = nbe (α ⇒' β) f2 := soundness f1_r_f2
        rewrite [← eq]; clear eq
        refine R.trans ?_ f1_r_nbe
        exact f1_r_f2.symm
      · intro e' Re'
        rewrite [← βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app R.refl)]
        rcases R_f1 with ⟨_, h0⟩
        exact h0 e' Re'

    · intro R_f2
      apply And.intro
      · have f2_r_nbe := Red_R_nbe R_f2; clear R_f2
        -- R-rewriting here:
        -- f1 ~ f2 ~ nbe f2 = nbe f1
        -- "rewrite [f1_r_f2, f2_r_nbe, ← soundness f1_r_f2]"
        have eq : nbe (α ⇒' β) f1 = nbe (α ⇒' β) f2 := soundness f1_r_f2
        rewrite [eq]; clear eq
        exact f1_r_f2.trans f2_r_nbe
      · intro e' Re'
        rewrite [βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app R.refl)]
        rcases R_f2 with ⟨_, h0⟩
        exact h0 e' Re'

lemma Red_numeral : Red nat (numeral n) :=
  by
  unfold Red
  induction n
  case zero => exact R.refl

  case succ n' IH =>
    unfold numeral
    -- R-rewriting here
    -- succ ⬝ numeral n' ~ succ ⬝ nbe (numeral n') = nbe (succ ⬝ numeral n')
    -- "rewrite [IH, nbe]"
    have eq : nbe nat (succ ⬝ numeral n') = succ ⬝ (nbe nat $ numeral n') := rfl; rewrite [eq]; clear eq
    apply (R.refl).app
    exact IH

-- for all e, Red a e
lemma all_Red {e : Exp a} : Red a e :=
  by
  induction e
  all_goals clear a
  case K a b =>
    apply And.intro
    · exact R.refl
    · intro e' Re'
      apply And.intro
      · have e'_r_nbe := Red_R_nbe Re'; clear Re'
        -- R-rewriting here
        -- K ⬝ e' ~ K ⬝ nbe e' = nbe (K ⬝ e')
        -- "rewrite [e'_r_nbe, nbe]"
        have eq : nbe (b ⇒' a) (K ⬝ e') = K ⬝ nbe a e' := rfl; rewrite [eq]; clear eq
        apply R.app R.refl
        exact e'_r_nbe
      · intro e'' _
        --R-rewriting here
        -- R (K ⬝ e' ⬝ e'') = R e'
        -- "rewrite [R.K]"
        rewrite [Red_resp (K ⬝ e' ⬝ e'') e' R.K]
        exact Re'

  case S a b c =>
    apply And.intro
    · exact R.refl
    · intro x Rx
      apply And.intro
      · have eq : nbe ((a ⇒' b) ⇒' a ⇒' c) (S ⬝ x) = S ⬝ nbe (a ⇒' b ⇒' c)  x := rfl; rewrite [eq]; clear eq
        -- R-rewriting here
        apply R.app R.refl
        exact Red_R_nbe Rx
      · intro y Ry
        apply And.intro
        · have eq : nbe (a ⇒' c) (S ⬝ x ⬝ y) = S ⬝ nbe (a ⇒' b ⇒' c) x ⬝ nbe (a ⇒' b) y := rfl; rewrite [eq]; clear eq
          replace Rx := Red_R_nbe Rx; replace Ry := Red_R_nbe Ry
          -- R-rewriting here
          have Sx_r_S_nbex : R (S ⬝ x) (S ⬝ (nbe (a ⇒' b ⇒' c) x)) := (R.refl).app Rx
          exact Sx_r_S_nbex.app Ry
        · intro z Rz
          -- R-rewriting here
          apply (Red_resp (S ⬝ x ⬝ y ⬝ z) _ R.S).mpr
          rcases Rx with ⟨_, Rxz⟩; specialize Rxz z Rz
          rcases Ry with ⟨_, Ryz⟩; specialize Ryz z Rz
          rcases Rxz with ⟨_, Rxzyz⟩; specialize Rxzyz (y ⬝ z) Ryz
          exact Rxzyz

  case app α β f x Rf Rx =>
    rcases Rf with ⟨_, h0⟩
    exact h0 x Rx

  case zero =>
    exact R.refl

  case succ =>
    apply And.intro
    · exact R.refl
    · intro x Rx
      unfold Red
      have eq : nbe nat (succ ⬝ x) = succ ⬝ (nbe nat x) := rfl; rewrite [eq]; clear eq
      -- R-rewriting here
      exact (R.refl).app Rx

  case recN α =>
    apply And.intro
    · exact R.refl
    · intro e' Re'
      apply And.intro
      · have eq : nbe ((nat ⇒' α ⇒' α) ⇒' nat ⇒' α) (recN ⬝ e') = recN ⬝ nbe α e' := rfl; rewrite [eq]; clear eq
        -- R-rewriting here
        apply R.app R.refl
        exact Red_R_nbe Re'
      · intro e'' Re''
        apply And.intro
        · have eq : nbe (nat ⇒' α) (recN ⬝ e' ⬝ e'') = recN ⬝ nbe α e' ⬝ nbe (nat ⇒' α ⇒' α) e'' := rfl; rewrite [eq]; clear eq
          replace Re' := Red_R_nbe Re'; replace Re'' := Red_R_nbe Re''
          -- R-rewriting here
          have h0 : R (recN ⬝ e') (recN ⬝ nbe α e') := (R.refl).app Re'
          exact h0.app Re''
        · intro n Rn
          have n_r_nbe := Rn; unfold R at n_r_nbe
          -- "rewrite [n_r_nbe]"
          rewrite [Red_resp (recN ⬝ e' ⬝ e'' ⬝ n) (recN ⬝ e' ⬝ e'' ⬝ (nbe nat n)) (R.refl.app n_r_nbe)]
          unfold nbe; simp [reify]
          induction ((Exp_inter nat n))
          · unfold numeral
            -- R-rewriting here
            exact (Red_resp (recN ⬝ e' ⬝ e'' ⬝ zero) e' R.recN_zero).mpr Re'
          · rename_i n' IH
            apply (Red_resp (.recN ⬝ e' ⬝ e'' ⬝ (.succ ⬝ numeral n')) (e'' ⬝ (numeral n') ⬝ (.recN ⬝ e' ⬝ e'' ⬝ (numeral n'))) R.recN_succ).mpr
            have R_numeral_n' : Red nat (numeral n') := by exact Red_numeral
            rcases Re'' with ⟨left, h0⟩; clear left
            specialize h0 (numeral n') R_numeral_n'
            rcases h0 with ⟨left, h0⟩; clear left
            exact h0 (.recN ⬝ e' ⬝ e'' ⬝ numeral n') IH

-- e ~ nbe a e
lemma R_nbe {e : Exp a} : R e (nbe a e) := Red_R_nbe all_Red

-- nbe a e = nbe a e' implies e ~ e'
lemma completeness : nbe a e = nbe a e' → R e e' :=
  by
  intro eq
  -- R-rewriting here
  -- e ~ nbe e = nbe e' ~ e'
  -- "rewrite [R_nbe, eq, ← R_nbe]"
  apply (R_nbe).trans
  rewrite [eq]; clear eq
  exact R_nbe.symm

-- e ~ e' ↔ nbe a e = nbe a e'
lemma correctness {e e' : Exp a} : R e e' ↔ nbe a e = nbe a e' := ⟨soundness, completeness⟩
