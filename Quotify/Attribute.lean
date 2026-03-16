module
public import Lean.Meta.Basic
public import Quotify.Setoid

open Lean Meta Std

namespace Quotify.Extension

public structure Proofs where
  equiv?     : Option Expr := none
  compatThms : List Name   := []

-- **TODO** The universe levels of the `BinRel`s are normalized, but those of the equivalence proofs
--          are not.
public abbrev Info := HashMap BinRel Proofs

public def Info.getEquiv? (info : Info) (binRel : BinRel) : Option Expr := do
  let some proofs := info[binRel]? | none
  proofs.equiv?

public inductive Entry.Val where
  | equiv (proof : Expr)
  | theorem (name : Name)
  deriving Inhabited

public structure Entry where
  key : BinRel
  val : Entry.Val
  deriving Inhabited

def Info.addEntry (info : Info) (entry : Entry) : Info :=
  info.alter entry.key fun proofs? =>
    match proofs?, entry.val with
    | none,        .equiv proof  => some { equiv? := proof }
    | none,        .theorem name => some { compatThms := [name] }
    | some proofs, .equiv proof  => some { proofs with equiv? := proof }
    | some proofs, .theorem name => some { proofs with compatThms := proofs.compatThms.concat name }

-- Note: We expect `rel` to be fully applied.
public def Info.getRelevantProofs (info : Info) (rel : Expr) : MetaM (Option Expr × List Name) := do
  let mut equiv? : Option Expr := none
  let mut compatThms : List Name := []
  for (binRel, proofs) in info do
    let some { params, levels } ← binRel.unify? rel | continue
    compatThms := compatThms ++ proofs.compatThms
    -- Only try to obtain an equivalence proof if we do not already have one.
    unless equiv?.isNone do continue
    let some equiv := proofs.equiv? | continue
    -- **TODO** What about level parameters?
    let equiv ← instantiateLambda equiv params
    equiv? := equiv
  return (equiv?, compatThms)

end Extension

open Extension

public abbrev Extension := SimpleScopedEnvExtension Entry Info

def Extension.mk : IO Extension :=
  registerSimpleScopedEnvExtension {
    initial  := ∅
    addEntry := Info.addEntry
  }

public def Extension.info (ex : Extension) : MetaM Info := do
  let env ← getEnv
  return ex.getState env

public initialize extension : Extension ← Extension.mk

namespace Attribute

inductive Target.Val where
  | equiv (proof : Expr)
  | theorem (resolvedDeclName : Name)

structure Target where
  binRel : BinRel
  val    : Target.Val

def Target.forDecl (resolvedDeclName : Name) : MetaM Target := do
  match ← getConstInfo resolvedDeclName with
  | .defnInfo defInfo =>
    let some setoid ← Setoid.forDef? defInfo
      | throwError "You can only use the `[quotify]` attribute on definitions of \
                    `{.ofConstName ``Setoid}`s."
    let binRel ← setoid.binRel
    let equivProof ← setoid.equivProof
    return { binRel, val := .equiv equivProof }
  | .thmInfo thmInfo =>
    let some binRel ← BinRel.forThm? thmInfo
      | throwError "You can only use the `[quotify]` attribute on theorems of the form \
                  `∀ … lhs rhs, r … lhs rhs` where `r …` is a homogeneous binary relation."
    return { binRel, val := .theorem resolvedDeclName }
  | _ => throwError "You can only use the `[quotify]` attribute on theorems or definitions, but \
                     `{.ofConstName resolvedDeclName}` is neither."

end Attribute

open Attribute

def Extension.addTarget (ex : Extension) (tgt : Target) (attrKind : AttributeKind) : MetaM Unit :=
  match tgt.val with
  | .theorem declName =>
    ex.add { key := tgt.binRel, val := .theorem declName } attrKind
  | .equiv proof => do
    let info ← extension.info
    let equiv? := info.getEquiv? tgt.binRel
    if equiv?.isSome then
      throwError "There already exists a `{.ofConstName ``Setoid}` marked with `[quotify]` for \
                  the relation {indentExpr tgt.binRel.expr}"
    else
      ex.add { key := tgt.binRel, val := .equiv proof } attrKind

def addQuotifyAttribute (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  recordExtraModUseFromDecl (isMeta := false) declName
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  let tgt ← Target.forDecl resolvedDeclName
  extension.addTarget tgt attrKind

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name := `quotify
    descr := "The `[quotify]` attribute is used to annotate `Setoid`s of equivalence relations for \
              for use with the `quotify` tactic, as well as theorems which prove compatability of \
              given functions with those equivalence relations."
    applicationTime := .afterCompilation
    add declName stx attrKind := MetaM.run' <| withRef stx <| addQuotifyAttribute declName attrKind
  }
