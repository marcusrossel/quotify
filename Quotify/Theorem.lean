module
public import Lean.Meta.Basic
public import Quotify.BinRel
import Quotify.Mathlib

open Lean Meta

namespace Quotify

-- **TODO** Add some flexibility to the order of parameters in theorem kinds.

public inductive Theorem.Kind where
  /-- Theorems of the form `∀ …, ∀ a b, (a ≈ b) → f a = f b`. -/
  | lift
  /-- Theorems of the form `∀ …, ∀ a₁ b₁ a₂ b₂, (a₁ ≈ a₂) → (b₁ ≈ b₂) → f a₁ b₁ = f a₂ b₂`. -/
  | lift₂
  /-- Theorems of the form `∀ …, ∀ a b, (a ≈ b) → f a ≈ f b`. -/
  | map
  /-- Theorems of the form `∀ …, ∀ a₁ a₂, (a₁ ≈ a₂) → ∀ b₁ b₂, (b₁ ≈ b₂) → f a₁ b₁ ≈ f a₂ b₂`. -/
  | map₂
  deriving BEq, Hashable, Inhabited

public instance Theorem.Kind.instToString : ToString Theorem.Kind where
  toString
    | .lift  => "lift"
    | .lift₂ => "lift₂"
    | .map   => "map"
    | .map₂  => "map₂"

public structure Theorem where
  declName       : Name
  numParams      : Nat
  numLevelParams : Nat
  deriving BEq, Inhabited

namespace Theorem

def isMap₂ (mvars : Array Expr) (lhs rhs : Expr) (binRel : BinRel) : MetaM (Option Nat) := do
  let numTargets := 6
  let [a₁, a₂, aEquiv, b₁, b₂, bEquiv] := mvars[(mvars.size - numTargets)...mvars.size].toList | return none
  let .app (.app f₁ a₁') b₁' := lhs | return none
  let .app (.app f₂ a₂') b₂' := rhs | return none
  unless f₁ == f₂ && a₁ == a₁' && a₂ == a₂' && b₁ == b₁' && b₂ == b₂' do return none
  let aEquivType ← inferType aEquiv
  let bEquivType ← inferType bEquiv
  let .success aEquivRel _ ← BinRel.fromFullyApplied aEquivType | return none
  let .success bEquivRel _ ← BinRel.fromFullyApplied bEquivType | return none
  unless binRel == aEquivRel && aEquivRel == bEquivRel do return none
  let numParams := mvars.size - numTargets
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == aEquivRel.numParams do return none
  return numParams

def isMap (mvars : Array Expr) (lhs rhs : Expr) (binRel : BinRel) : MetaM (Option Nat) := do
  let numTargets := 3
  let [a, b, equiv] := mvars[(mvars.size - numTargets)...mvars.size].toList | return none
  let .app f₁ a' := lhs | return none
  let .app f₂ b' := rhs | return none
  unless f₁ == f₂ && a == a' && b == b' do return none
  let equivType ← inferType equiv
  let .success equivRel _ ← BinRel.fromFullyApplied equivType | return none
  unless binRel == equivRel do return none
  let numParams := mvars.size - numTargets
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == equivRel.numParams do return none
  return numParams

public def forThm? (thmInfo : TheoremVal) : MetaM <| Option (Theorem × Kind × BinRel) := do
  let thmType := thmInfo.type.cleanupAnnotations
  let (mvars, _, body) ← forallMetaTelescopeReducing thmType
  let #[lhs, rhs] := body.getBoundedAppArgs 2 | return none
  let rel := body.stripArgsN 2
  let .success binRel _ ← BinRel.fromExpr rel | return none
  if let some numParams ← isMap mvars lhs rhs binRel then
    let thm := { declName := thmInfo.name, numParams, numLevelParams := thmInfo.levelParams.length }
    return some (thm, .map, binRel)
  else if let some numParams ← isMap₂ mvars lhs rhs binRel then
    let thm := { declName := thmInfo.name, numParams, numLevelParams := thmInfo.levelParams.length }
    return some (thm, .map₂, binRel)
  else
    return none

public structure Simp where
  declName : Name
  expr     : Expr

def mkFreshExprMVars (num : Nat) : MetaM (Array Expr) :=
  num.foldM (init := #[]) fun _ _ acc => return acc.push (← mkFreshExprMVar none)

def mvarApplied (thm : Theorem) : MetaM Expr := do
  let lmvars ← mkFreshLevelMVars thm.numLevelParams
  let mvars ← mkFreshExprMVars thm.numParams
  return mkAppN (.const thm.declName lmvars) mvars

public def simp (thm : Theorem) : Theorem.Kind → MetaM Theorem.Simp
  | .map => do
    let quotientMapMk ← mkConstWithFreshMVarLevels ``Quotient.map_mk
    let mvars ← mkFreshExprMVars 5
    let compatThm ← thm.mvarApplied
    let args := mvars.push compatThm
    let expr := mkAppN quotientMapMk args
    return { declName := thm.declName, expr }
  | .map₂ => do
    let quotientMap₂Mk ← mkConstWithFreshMVarLevels ``Quotient.map₂_mk
    let mvars ← mkFreshExprMVars 7
    let compatThm ← thm.mvarApplied
    let args := mvars.push compatThm
    let expr := mkAppN quotientMap₂Mk args
    return { declName := thm.declName, expr }
  | _ =>
    -- **TODO**
    return { declName := .anonymous, expr := mkNatLit 0 }
