module
public import Lean.Meta.Basic
public import Quotify.BinRel
import Quotify.Mathlib

open Lean Meta

namespace Quotify.Theorem

-- **TODO** Add some flexibility to the order of parameters in theorem kinds.

public inductive Kind where
  /-- Theorems of the form `∀ …, ∀ a b, (a ≈ b) → f a = f b`. -/
  | lift
  /-- Theorems of the form `∀ …, ∀ a₁ b₁ a₂ b₂, (a₁ ≈ a₂) → (b₁ ≈ b₂) → f a₁ b₁ = f a₂ b₂`. -/
  | lift₂
  /-- Theorems of the form `∀ …, ∀ a b, (a ≈ b) → f a ≈ f b`. -/
  | map
  /-- Theorems of the form `∀ …, ∀ a₁ a₂, (a₁ ≈ a₂) → ∀ b₁ b₂, (b₁ ≈ b₂) → f a₁ b₁ ≈ f a₂ b₂`. -/
  | map₂
  deriving BEq, Hashable, Inhabited

public instance Kind.instToString : ToString Theorem.Kind where
  toString
    | .lift  => "lift"
    | .lift₂ => "lift₂"
    | .map   => "map"
    | .map₂  => "map₂"

/--
Creates a list of `n` fresh mvars of the given `type`, where `n` is the number of arguments expected
by the function in a theorem of the given `Kind`. For example, for `Kind.map` this is `1` and for
`Kind.map₂` it is `2`.
-/
public def Kind.freshArgMVars (type : Expr) : Kind → MetaM (Array Expr)
  | .map  | .lift  => return #[← mkFreshExprMVar type]
  | .map₂ | .lift₂ => return #[← mkFreshExprMVar type, ← mkFreshExprMVar type]

public structure Function where
  /-- An (abstraction over) the target function (called `f` in the documentation comments on
     `Theorem.Kind`) of the given theorem. Thus `fn` has the form `λ a₁ … aₙ, f a₁ … aₙ` where
     `a₁ … aₙ` are the arguments parameterizing the theorem (the `…` in the documentation comments
     on `Theorem.Kind`). -/
  fn : Expr
  /-- The number of arguments parameterizing `fn`. For `λ a₁ … aₙ, f a₁ … aₙ` where we have
      `numParams = n`. If `f a₁ … aₙ` is itself a `λ` with two arguments, we get
      `λ a₁ … aₙ lhs rhs, … lhs rhs`, but still have `numParams = n`. -/
  numParams : Nat
  deriving BEq, Inhabited

public structure _root_.Quotify.Theorem extends Function where
  declName : Name
  /-- The names of the level parameters over the theorem (and thus, potentially `fn`) is abstracted.
      Note, this field is unrelated to `numParams`. -/
  levelParams : List Name
  deriving BEq, Inhabited

def lift? (mvars : Array Expr) (lhs rhs : Expr) : MetaM <| Option (Theorem.Function × BinRel) := do
  let targetsStartIdx := mvars.size - 3
  let [a, b, equiv] := mvars[targetsStartIdx...mvars.size].toList | return none
  let .app f₁ a' := lhs | return none
  let .app f₂ b' := rhs | return none
  unless f₁ == f₂ && a == a' && b == b' do return none
  let equivType ← inferType equiv
  let .success equivRel _ ← BinRel.fromFullyApplied equivType | return none
  let params := mvars[0...targetsStartIdx]
  let numParams := params.size
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == equivRel.numParams do return none
  let fn ← mkLambdaFVars params f₁
  return some ({ fn, numParams }, equivRel)

-- **TODO** Ensure that `fᵢ` is not itself a parameter?
def lift₂? (mvars : Array Expr) (lhs rhs : Expr) : MetaM <| Option (Theorem.Function × BinRel) := do
  let targetsStartIdx := mvars.size - 6
  let [a₁, a₂, b₁, b₂, aEquiv, bEquiv] := mvars[targetsStartIdx...mvars.size].toList | return none
  let .app (.app f₁ a₁') b₁' := lhs | return none
  let .app (.app f₂ a₂') b₂' := rhs | return none
  unless f₁ == f₂ && a₁ == a₁' && a₂ == a₂' && b₁ == b₁' && b₂ == b₂' do return none
  let aEquivType ← inferType aEquiv
  let bEquivType ← inferType bEquiv
  let .success aEquivRel _ ← BinRel.fromFullyApplied aEquivType | return none
  let .success bEquivRel _ ← BinRel.fromFullyApplied bEquivType | return none
  -- **TODO** This need not be the same equivalence relation.
  unless aEquivRel == bEquivRel do return none
  let params := mvars[0...targetsStartIdx]
  let numParams := params.size
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == aEquivRel.numParams do return none
  let fn ← mkLambdaFVars params f₁
  return some ({ fn, numParams }, aEquivRel)

-- **TODO** Ensure that `fᵢ` is not itself a parameter?
def map? (mvars : Array Expr) (lhs rhs : Expr) (binRel : BinRel) : MetaM (Option Theorem.Function) := do
  let targetsStartIdx := mvars.size - 3
  let [a, b, equiv] := mvars[targetsStartIdx...mvars.size].toList | return none
  let .app f₁ a' := lhs | return none
  let .app f₂ b' := rhs | return none
  unless f₁ == f₂ && a == a' && b == b' do return none
  let equivType ← inferType equiv
  let .success equivRel _ ← BinRel.fromFullyApplied equivType | return none
  -- **TODO** This need not be the same equivalence relation.
  unless binRel == equivRel do return none
  let params := mvars[0...targetsStartIdx]
  let numParams := params.size
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == equivRel.numParams do return none
  let fn ← mkLambdaFVars params f₁
  return some { fn, numParams }

-- **TODO** Ensure that `fᵢ` is not itself a parameter?
def map₂? (mvars : Array Expr) (lhs rhs : Expr) (binRel : BinRel) : MetaM (Option Theorem.Function) := do
  let targetsStartIdx := mvars.size - 6
  let [a₁, a₂, aEquiv, b₁, b₂, bEquiv] := mvars[targetsStartIdx...mvars.size].toList | return none
  let .app (.app f₁ a₁') b₁' := lhs | return none
  let .app (.app f₂ a₂') b₂' := rhs | return none
  unless f₁ == f₂ && a₁ == a₁' && a₂ == a₂' && b₁ == b₁' && b₂ == b₂' do return none
  let aEquivType ← inferType aEquiv
  let bEquivType ← inferType bEquiv
  let .success aEquivRel _ ← BinRel.fromFullyApplied aEquivType | return none
  let .success bEquivRel _ ← BinRel.fromFullyApplied bEquivType | return none
  -- **TODO** This need not be the same equivalence relation.
  unless binRel == aEquivRel && aEquivRel == bEquivRel do return none
  let params := mvars[0...targetsStartIdx]
  let numParams := params.size
  -- This is a low-effort check that the theorem's leading parameters are (at least the same number
  -- as) those abstracting the equivalence relation.
  unless numParams == aEquivRel.numParams do return none
  let fn ← mkLambdaFVars params f₁
  return some { fn, numParams }

public def forThm? (thmInfo : TheoremVal) : MetaM <| Option (Theorem × Kind × BinRel) := do
  let thmType := thmInfo.type.cleanupAnnotations
  let (mvars, _, body) ← forallMetaTelescopeReducing thmType
  let #[lhs, rhs] := body.getBoundedAppArgs 2 | return none
  let rel := body.stripArgsN 2
  if rel.isAppOfArity ``Eq 1 then
    if let some (f, binRel) ← lift? mvars lhs rhs then
      let thm := { f with declName := thmInfo.name, levelParams := thmInfo.levelParams }
      return some (thm, .lift, binRel)
    else if let some (f, binRel) ← lift₂? mvars lhs rhs then
      let thm := { f with declName := thmInfo.name, levelParams := thmInfo.levelParams }
      return some (thm, .lift₂, binRel)
  else if let .success binRel _ ← BinRel.fromExpr rel then
    if let some f ← map? mvars lhs rhs binRel then
      let thm := { f with declName := thmInfo.name, levelParams := thmInfo.levelParams }
      return some (thm, .map, binRel)
    else if let some f ← map₂? mvars lhs rhs binRel then
      let thm := { f with declName := thmInfo.name, levelParams := thmInfo.levelParams }
      return some (thm, .map₂, binRel)
  return none

/--
Given `thm.fn` of the form `λ a₁ … aₙ, f a₁ … aₙ`, instantiates the binders with mvars and returns
`(params : Array Expr) × (lmvars : List Level) × (fn : Expr)` with `params` being the mvars for
`a₁ … aₙ`, `lmvars` being the the level mvars instantiated for `thm.levelParams`, and `fn` being
instantiated to `f params`.
-/
def metaTelescope (thm : Theorem) : MetaM (Array Expr × List Level × Expr) := do
  -- It's important that we instantiate the level params with level mvars *before* we telescope, as
  -- otherwise the types of the created (expr) mvars still refer to the level params.
  let freshLMVars     ← mkFreshLevelMVars thm.levelParams.length
  let fn             := thm.fn.instantiateLevelParams thm.levelParams freshLMVars
  let (params, _, fn) ← lambdaMetaTelescope fn (maxMVars? := thm.numParams)
  return (params, freshLMVars, fn)

structure Match where
  params : Array Expr
  levels : List Level

/--
Tries to match a given `target` against a `thm`'s `fn` up to definitional equality. If the match
succeeds a substitution (a `Match`) for `target`'s parameters is returned.

Matching is asymmetric in that the `thm.fn` must be more abstract than the `target`. For example,
`thm.fn = λ α, @List.reverse α` will match `target = @List.reverse Nat`, but not the other way
around.
-/
def match? (thm : Theorem) (target : Expr) : MetaM (Option Match) := do
  -- We bump the mvar context depth so that only `thm.fn`s (abstracted) parameters can be matched
  -- but not the other way around. For example, this means that `@List.reverse ?α` can be matched
  -- against `@List.reverse Nat`, but not vice versa.
  withNewMCtxDepth do
    let (params, lmvars, fn) ← thm.metaTelescope
    if ← isDefEq fn target then
      let params ← params.mapM instantiateMVars
      let levels ← lmvars.mapM instantiateLevelMVars
      return some { params, levels }
    else
      return none

/--
Checks that the given `thm.fn` matches the given `target`, and if so produces a proof for `thm`
specialized to the `target`. For example, if `thm.fn` is
`∀ α a b, a ≈ b → List.reverse a ≈ List.reverse b` and `target` is `@List.reverse Nat`, then
`specialize?` produces a proof of `∀ a b, a ≈ b → @List.reverse Nat a ≈ @List.reverse Nat b`.

Note that for theorems where `fn` is not parameterized, this function amounts to just checking that
the `thm` is applicable to the `target` and returning the "default" proof.
-/
def specialize? (thm : Theorem) (target : Expr) : MetaM (Option Expr) := do
  let some m ← thm.match? target | return none
  return mkAppN (.const thm.declName m.levels) m.params

-- **DOC**
public def mkPush? (thm : Theorem) (app : Expr) (setoid : Expr) : Theorem.Kind → MetaM (Option Expr)
  | .map => do
    let .app fn arg := app | return none
    let some h ← thm.specialize? fn | return none
    let argType ← inferType arg
    let lvl ← getLevel argType
    let eq := mkApp7 (.const ``Quotient.map_mk [lvl, lvl]) argType argType setoid setoid fn h arg
    mkEqSymm eq
  | .map₂ => do
    let .app (.app fn arg₁) arg₂ := app | return none
    let some h ← thm.specialize? fn | return none
    let argType ← inferType arg₁
    let lvl ← getLevel argType
    let eq := mkApp10 (.const ``Quotient.map₂_mk [lvl, lvl, lvl]) argType argType argType setoid setoid setoid fn h arg₁ arg₂
    mkEqSymm eq
  | _ =>
    return none -- **TODO**
