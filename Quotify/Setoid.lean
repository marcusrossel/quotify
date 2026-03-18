module
public import Quotify.BinRel

open Lean Meta

namespace Quotify

public protected structure Setoid where
  /-- For `∀ …, Setoid τ`, this `type` is `λ …, τ`. -/
  type : Expr
  /-- An expression of type `λ …, Setoid (type …)`. -/
  inst : Expr

namespace Setoid

def metaTelescope (setoid : Quotify.Setoid) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  let (params, _, type) ← lambdaMetaTelescope setoid.type
  let inst := mkAppN setoid.inst params
  k params type inst

public structure Equiv where
  proof : Expr
  -- We keep an `Equiv` abstracted over the same level parameters as its corresponding `BinRel`.
  levelParams : List Name

public def components? (setoid : Quotify.Setoid) : MetaM <| Option (BinRel × Equiv) :=
  setoid.metaTelescope fun params type inst => do
    let level  ← getLevel type
    -- Construct the `BinRel`.
    let rel   := mkApp2 (.const ``Setoid.r [level]) type inst
    let lhs    ← mkFreshExprMVar type
    let rhs    ← mkFreshExprMVar type
    let fullyAppliedRel := mkApp2 rel lhs rhs
    let .success binRel levelParamNorm ← BinRel.fromFullyApplied fullyAppliedRel | return none
    -- Construct the `Equiv`.
    let proof := mkApp2 (.const ``Setoid.iseqv [level]) type inst
    let proof  ← mkLambdaFVars params proof
    -- Normalize the level parameters of `proof` in the same way as for `rel`, by using the
    -- `levelParamNorm` obtained from `BinRel.fromFullyApplied`. We assume that the level parameters
    -- appearing in `proof` are a subset of those in `rel`.
    let normParams := levelParamNorm.normal.map mkLevelParam
    let proof := proof.instantiateLevelParams levelParamNorm.original normParams
    -- We keep the `Equiv` abstracted over the same level parameters as its corresponding `BinRel`.
    -- Note that `levelParamNorm.normal` should be the same as `binRel.levelParams`.
    let equiv := { proof, levelParams := levelParamNorm.normal }
    return some (binRel, equiv)

public def forDef? (defnInfo : DefinitionVal) : MetaM (Option Quotify.Setoid) :=
  forallTelescopeReducing defnInfo.type fun params body => do
    let_expr Setoid type := body | return none
    let inst := mkAppN defnInfo.value params
    let type ← mkLambdaFVars params type
    let inst ← mkLambdaFVars params inst
    return some { type, inst }
