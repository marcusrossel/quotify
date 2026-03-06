module
public import Lean.Meta.Basic
public import Quotify.BinRel

open Lean Meta

namespace Quotify.EquivRel

-- TODO: Make this prive once you delete the `#quotify_setoid` command.
public def getSetoid? (binRel : BinRel) : MetaM (Option Expr) := do
  binRel.telescope fun params _ argType => do
    let level ← getLevel argType
    let setoidType := mkApp (.const ``Setoid [level]) argType
    let instanceType ← mkForallFVars params setoidType
    synthInstance? instanceType

-- TODO: As we also need a proof of equivalence, this might need to be defined on some other type
--       than `BinRel`.
-- TODO: Update the doc comment.
/--
Given an `BinRel` of the form `λ a₁ … aₙ, r a₁ … aₙ`, returns the corresponding relation over
quotients `λ a₁ … aₙ lhs rhs, Quot.mk (r a₁ … aₙ) lhs = Quot.mk (r a₁ … aₙ) rhs`.
-/
public def quotify (binRel : BinRel) : MetaM Expr := do
  -- TODO: Construct a Setoid on the fly and use `Quotient`.
  binRel.telescope fun params rel argType => do
    withLocalDecl `lhs .default argType fun lhs => do
      withLocalDecl `rhs .default argType fun rhs => do
        let eqLhs ← mkAppM ``Quot.mk #[rel, lhs]
        let eqRhs ← mkAppM ``Quot.mk #[rel, rhs]
        let eq ← mkEq eqLhs eqRhs
        let vars := params ++ #[lhs, rhs]
        mkLambdaFVars vars eq
