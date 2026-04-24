import Quotify.Tactic
import Quotify.Command
import Quotify.Unexpanders

@[quotify]
theorem t (l₁ l₂ : List α) (h : l₁ ≈ l₂) : l₁.reverse ≈ l₂.reverse := sorry

attribute [quotify] List.isSetoid

open Lean Meta Elab Term Simp

def pushT : Simproc := fun e => do
  let_expr Quotient.mk listType setoid app := e | return .continue
  let .app fn l := app | return .continue

  let lvl ← getLevel listType
  let thm := mkApp (.const ``t [lvl]) listType

  let prf := mkApp7 (.const ``Quotient.map_mk [lvl, lvl]) listType listType setoid setoid fn thm l
  let prf ← mkEqSymm prf
  let_expr Eq _ _ pushed := ← inferType prf | return .continue
  return .visit { expr := pushed, proof? := prf }

#eval do
  -- following elabSimprocKeys
  let pattern : Expr ← elabTerm (← `(@Quotient.mk _ _ _)) none
  Term.synthesizeSyntheticMVars
  let keys ← withSimpGlobalConfig <| DiscrTree.mkPath pattern
  registerSimproc ``pushT keys

example (l₁ l₂ : List α) (h : l₁.reverse ≈ l₂.reverse) : l₁ ≈ l₂ := by
  quotify
  simp only [↓pushT] at *
  sorry
