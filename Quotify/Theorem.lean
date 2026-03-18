module
public import Lean.Meta.Basic

open Lean

namespace Quotify

public inductive Theorem.Kind where
  | map
  deriving BEq, Hashable, Inhabited

public structure Theorem where
  kind      : Theorem.Kind
  numParams : Nat

namespace Theorem

public def forThm? (thm : TheoremVal) : MetaM (Option Theorem) := do
  -- **TODO**
  return some { kind := .map, numParams := 0 }
