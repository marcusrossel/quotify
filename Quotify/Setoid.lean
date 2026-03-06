module
public import Lean.Meta.Basic
public import Quotify.BinRel

open Lean Meta

namespace Quotify

-- **TODO** We might have different `Setoid`s with the same name, depending on how they are applied.
-- For example, `@List.isSetoid Bool` and `@List.isSetoid Nat`. And notably, they denote different
-- relations.
#check (List.isSetoid _).r
#check (List.isSetoid Bool).r
#check (List.isSetoid Nat).r

public abbrev Setoid := Expr

-- TODO: Make this private once you delete the `#quotify_setoid` command.
public def Setoid.ofBinRel? (binRel : BinRel) : MetaM (Option Setoid) := do
  binRel.telescope fun params _ argType => do
    let level ← getLevel argType
    let setoidType := mkApp (.const ``Setoid [level]) argType
    let instanceType ← mkForallFVars params setoidType
    let some expr ← synthInstance? instanceType | return none
    let expr ← etaExpand expr
    sorry

-- TODO: Update the doc comment.
/--
Given an `BinRel` of the form `λ a₁ … aₙ, r a₁ … aₙ`, returns the corresponding relation over
quotients `λ a₁ … aₙ lhs rhs, Quot.mk (r a₁ … aₙ) lhs = Quot.mk (r a₁ … aₙ) rhs`.
-/
public def quotify (binRel : BinRel) : MetaM Expr := do
  -- TODO: Fetch the setoid and use `Quotient`.
  binRel.telescope fun params rel argType => do
    withLocalDecl `lhs .default argType fun lhs => do
      withLocalDecl `rhs .default argType fun rhs => do
        let eqLhs ← mkAppM ``Quot.mk #[rel, lhs]
        let eqRhs ← mkAppM ``Quot.mk #[rel, rhs]
        let eq ← mkEq eqLhs eqRhs
        let vars := params ++ #[lhs, rhs]
        mkLambdaFVars vars eq
