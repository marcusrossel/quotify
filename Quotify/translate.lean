module
import Lean
public meta import Quotify.ReplaceR
public meta import Quotify.Signature

open Lean Elab Tactic Term Meta

meta def translateF (R : Name) (R_Setoid : Name) (resp_list : Array (Name × Name)) : TacticM Unit := do
  --Step 1: Replace all instances of "R x₁⋯xₙ a b" with "⟦a⟧ = ⟦b⟧"
  replace_R R R_Setoid

  --Step 2: For each respectful func, add "func_eq" to a list
  let mut eq_list := []
  for (f, f_sig) in resp_list do
    let eq := mkIdent (← letSignature (mkConst R_Setoid) f f_sig)
    eq_list := eq_list.concat eq

  -- Step 3:
  -- For each eq in eq_list:
  --  if "simp only [← $eq] at *" succeeds:
  --    restart the for-loop
  --  else:
  --    continue
  --
  -- This replaces all functions with their Quotient-versions
  let mut restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [← $eq] at *)))
        restart := true
      catch _err => continue

  -- Step 4:
  -- eq_list is no longer
  -- needed in Local-Context
  for eq in eq_list do
    (evalTactic (← `(tactic| clear $eq)))


elab "translateF" R:ident R_Setoid:ident sig_list:sig_list : tactic =>
  do
  let `(sig_list| [$[$sig_list],*]) := sig_list | unreachable!
  let sig_list := sig_list.map parse_entry
  translateF @R.getId @R_Setoid.getId sig_list



meta def translateB (_R : Name) (R_Setoid : Name) (resp_list : Array (Name × Name)) : TacticM Unit := do
  --Step 1: For each respectful func, add "func_eq" to a list
  let mut eq_list := []
  for (f, f_sig) in resp_list do
    let eq := mkIdent (← letSignature (mkConst R_Setoid)  f f_sig)
    eq_list := eq_list.concat eq

  -- Step 2:
  -- For each eq in eq_list:
  --  if "simp only [$eq] at *" succeeds:
  --    restart the for-loop
  --  else:
  --    continue
  --
  -- This translates the Quotient-functions back to their original versions.
  let mut restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [$eq:term] at *)))
        restart := true
      catch _err => continue

  -- Step 3:
  -- eq_list is no longer
  -- needed in Local-Context
  for eq in eq_list do
    (evalTactic (← `(tactic| clear $eq)))

  --Step 4: Replace all instances of "⟦a⟧ = ⟦b⟧" with "R x₁⋯xₙ a b"
  let R_Setoid := mkIdent R_Setoid
  evalTactic (← `(tactic| simp only [Quotient.eq, $R_Setoid:term] at *))

elab "translateB" R:ident R_Setoid:ident sig_list:sig_list : tactic =>
  do
  let `(sig_list| [$[$sig_list],*]) := sig_list | unreachable!
  let sig_list := sig_list.map parse_entry
  translateB R.getId R_Setoid.getId sig_list
