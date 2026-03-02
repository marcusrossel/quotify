import Lean
import Mathlib.Tactic

open Lean Elab Tactic Term Meta

-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → relation X
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- mkQuotientEq R R_Setoid := λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧
def mkQuotientEq (R : Name) (R_Setoid : Name) : MetaM Expr := do
  let R_Setoid  := (Expr.const R_Setoid [])

  let R     := Lean.mkConst R
  let RType := ← inferType R
  let n     := RType.getNumHeadForalls
  forallBoundedTelescope RType (some $ n+2) fun xs_e1_e2 _Prop => do
    let xs := xs_e1_e2.pop.pop
    let e1 := xs_e1_e2.pop.toList.getLast!
    let e2 := xs_e1_e2.toList.getLast!
    let X := ← inferType e2
    let bb_e1_dd := (← mkAppOptM ``Quotient.mk $ #[some X] ++ #[some $ mkAppN (R_Setoid) xs, e1])
    let bb_e2_dd := (← mkAppOptM ``Quotient.mk $ #[some X] ++ #[some $ mkAppN (R_Setoid) xs, e2])
    let eq := ← mkEq bb_e1_dd bb_e2_dd
    mkLambdaFVars xs_e1_e2 eq


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → relation X
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- mkR_Eq_Quotient R R_Setoid := R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧
def mkR_Eq_Quotient (R : Name) (R_Setoid : Name) : MetaM Expr := do
  let QuotientEq := ← mkQuotientEq R R_Setoid
  let R := .const R []
  mkEq R QuotientEq


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → relation X
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- Adds "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
def addR_eq (R : Name) (R_Setoid : Name) : TermElabM Unit := do
  -- Build the type "R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧"
  let type := ← mkR_Eq_Quotient R R_Setoid

  -- Elaborate automated tactic proof as an expression
  -- Ensuring there are no meta-variables (so kernel doesn't complain)
  let pf := ← elabTerm (← `(by
      funext
      apply propext
      apply Iff.intro
      exact λ h => Quotient.sound h
      exact λ h => Quotient.exact h
    )) (some type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf

  -- Add "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
  let env              := ← getEnv
  let restrictedPrefix := env.asyncPrefix?.casesOn' ("") (λ name => name.toString ++ ".")
  let decl := Declaration.thmDecl {
    name        := (restrictedPrefix ++ R.toString ++ "_eq").toName
    levelParams := []
    type        := type
    value       := pf
  }
  addDecl decl
elab "addR_eq" R:name R_Setoid:name : tactic => do addR_eq R.getName R_Setoid.getName

-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → relation X
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X
def replace_R (R : Name) (R_Setoid : Name) : TacticM Unit :=
  withMainContext do
    -- Add "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
    let env       := ← getEnv
    let restrictedPrefix := env.asyncPrefix?.casesOn' ("") (λ name => name.toString ++ ".")
    let R_eq      := (restrictedPrefix ++ R.toString ++ "_eq").toName
    if ! env.contains R_eq
    then
      addR_eq R R_Setoid

    -- Revert all localHyps (last-to-first localHyps)
    let localHyps := (← getLocalHyps).map (λ expr => (expr.fvarId!))
    let goal      := ← getMainGoal
    let (_, goal) := ← goal.revert (preserveOrder := True) (localHyps)
    replaceMainGoal [goal]

    -- Generalize on R
    let R_Ident    := mkIdent R
    let R'_Ident   := mkIdent (R.toString ++ "'").toName
    let eq_Ident  := mkIdent ("eq").toName
    evalTactic (← `(tactic | generalize $eq_Ident:ident : (@$R_Ident:ident) = $R'_Ident:ident))

    -- Rewrite "R_eq : R = R_eq : R = (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)"
    -- at "eq : R = R'"
    let R_eq_Ident := mkIdent R_eq
    evalTactic (← `(tactic | rewrite [($R_eq_Ident:ident)] at ($eq_Ident:ident)))

    -- Substitute "eq : (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)  =  R'" everywhere
    evalTactic (← `(tactic | subst ($eq_Ident:ident)))

    -- Beta-reduce the goal
    evalTactic (← `(tactic | beta_reduce))

    -- Re-intro all our localHyps (first-to-last localHyps)
    let goal      := ← getMainGoal
    let localHyps := (← localHyps.mapM (λ fvar => fvar.getUserName)).toList
    let n := localHyps.length
    let (_, goal) := ← goal.introN n (givenNames := localHyps)
    replaceMainGoal [goal]
elab "replace_R" R:ident R_Setoid:ident : tactic => do replace_R @R.getId @R_Setoid.getId
/-
Step 1: Revert EVERYTHING to get a single Target with an empty LocalCtxt

Step 2: Translate Target

Step 3: Intro EVERYTHING with all their original names

This avoids breaking anything due to dependent products.
This way we guarantee translating all "R"s in one single step.
-/
