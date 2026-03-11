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

def telescope (setoid : Quotify.Setoid) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α :=
  lambdaTelescope setoid.type fun params type => do
    let inst := mkAppN setoid.inst params
    k params type inst

def metaTelescope (setoid : Quotify.Setoid) (k : Expr → Expr → MetaM α) : MetaM α := do
  let (params, _, type) ← lambdaMetaTelescope setoid.type
  let inst := mkAppN setoid.inst params
  k type inst

public def binRel (setoid : Quotify.Setoid) : MetaM BinRel :=
  setoid.metaTelescope fun type inst => do
    let level ← getLevel type
    let rel  := mkApp2 (.const ``Setoid.r [level]) type inst
    let lhs   ← mkFreshExprMVar type
    let rhs   ← mkFreshExprMVar type
    let fullyAppliedRel := mkApp2 rel lhs rhs
    let .success binRel ← BinRel.fromFullyApplied fullyAppliedRel | throwError "TODO"
    return binRel

public def equivProof (setoid : Quotify.Setoid) : MetaM Expr :=
  setoid.telescope fun params type inst => do
    let level  ← getLevel type
    let proof := mkApp2 (.const ``Setoid.iseqv [level]) type inst
    mkLambdaFVars params proof

public def forDef? (defnInfo : DefinitionVal) : MetaM (Option Quotify.Setoid) :=
  forallTelescopeReducing defnInfo.type fun params body => do
    let_expr Setoid type := body | return none
    let inst := mkAppN defnInfo.value params
    let type ← mkLambdaFVars params type
    let inst ← mkLambdaFVars params inst
    return some { type, inst }

def synthForBinRel? (binRel : BinRel) : MetaM (Option Quotify.Setoid) := do
  binRel.telescope fun params _ argType => do
    let level ← getLevel argType
    let setoidType := mkApp (.const ``Setoid [level]) argType
    let instanceType ← mkForallFVars params setoidType
    let some expr ← synthInstance? instanceType | return none
    let expr ← etaExpand expr
    sorry
