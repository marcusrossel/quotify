module
public import Lean.Meta.Basic
public import Quotify.Setoid

open Lean Meta Std

namespace Quotify.Extension

public inductive Entry.Val where
  | equiv (proof : Expr)
  | theorem (name : Name)
  deriving Inhabited

public structure Entry.Item where
  key : BinRel
  val : Val
  deriving Inhabited

public inductive Entry.Kind where
  | add
  | erase
  deriving Inhabited

public structure Entry extends Entry.Item where
  kind : Entry.Kind
  deriving Inhabited

public structure Proofs where
  equiv?     : Option Expr := none
  compatThms : List Name   := []

-- **TODO** The universe levels of the `BinRel`s are normalized, but those of the equivalence proofs
--          are not.
public abbrev Info := HashMap BinRel Proofs

namespace Info

public def getEquiv? (info : Info) (binRel : BinRel) : Option Expr := do
  let some proofs := info[binRel]? | none
  proofs.equiv?

def addItem (info : Info) (item : Entry.Item) : Info :=
  info.alter item.key fun proofs? =>
    match proofs?, item.val with
    | none,        .equiv proof  => some { equiv? := proof }
    | none,        .theorem name => some { compatThms := [name] }
    | some proofs, .equiv proof  => some { proofs with equiv? := proof }
    | some proofs, .theorem name => some { proofs with compatThms := proofs.compatThms.concat name }

def eraseItem (info : Info) (item : Entry.Item) : Info :=
  info.alter item.key fun proofs? =>
    match proofs?, item.val with
    | none,        _             => none
    | some proofs, .equiv _      => some { proofs with equiv? := none }
    | some proofs, .theorem name => some { proofs with compatThms := proofs.compatThms.erase name }

def addEntry (info : Info) (entry : Entry) : Info :=
  match entry.kind with
  | .add   => info.addItem entry.toItem
  | .erase => info.eraseItem entry.toItem

public def getMatchingEquiv? (info : Info) (binRel : BinRel) : MetaM (Option Expr) := do
  for (pattern, proofs) in info do
    let some equiv := proofs.equiv? | continue
    -- **TODO** What about level parameters?
    let some { params, levels } ← pattern.match? binRel | continue
    let equiv ← instantiateLambda equiv params
    -- If `binRel` is not fully applied, then `params` will contain mvars for those arguments which
    -- are to remain abstracted. Thus, after instantiating params, we abstract these mvars again.
    let mvarParams := params.filter (·.isMVar)
    let equiv ← mkLambdaFVars mvarParams equiv
    return equiv
  return none

public def hasMatchingEquiv (info : Info) (binRel : BinRel) : MetaM Bool :=
  Option.isSome <$> info.getMatchingEquiv? binRel

public def getMatchingCompatThms (info : Info) (binRel : BinRel) : MetaM (List Name) := do
  let mut compatThms : List Name := []
  for (pattern, proofs) in info do
    unless (← pattern.match? binRel).isSome do continue
    compatThms := compatThms ++ proofs.compatThms
  return compatThms

end Extension.Info

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
    ex.add { key := tgt.binRel, kind := .add, val := .theorem declName } attrKind
  | .equiv proof => do
    let info ← extension.info
    if ← info.hasMatchingEquiv tgt.binRel then
      throwError "There already exists a `{.ofConstName ``Setoid}` marked with `[quotify]` for \
                  the relation {indentExpr tgt.binRel.expr}"
    ex.add { key := tgt.binRel, kind := .add, val := .equiv proof } attrKind

def Extension.eraseTarget (ex : Extension) (tgt : Target) : MetaM Unit :=
  match tgt.val with
  | .theorem declName => ex.add { key := tgt.binRel, kind := .erase, val := .theorem declName }
  -- Note, the `proof` is irrelevant here.
  | .equiv proof => ex.add { key := tgt.binRel, kind := .erase, val := .equiv proof }

def addQuotifyAttribute (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  recordExtraModUseFromDecl (isMeta := false) declName
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  let tgt ← Target.forDecl resolvedDeclName
  extension.addTarget tgt attrKind

def eraseQuotifyAttribute (declName : Name) : MetaM Unit := do
  let resolvedDeclName ← resolveGlobalConstNoOverloadCore declName
  let tgt ← Target.forDecl resolvedDeclName
  extension.eraseTarget tgt

initialize
  -- **TODO** I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name := `quotify
    descr := "The `[quotify]` attribute is used to annotate `Setoid`s of equivalence relations for \
              for use with the `quotify` tactic, as well as theorems which prove compatability of \
              given functions with those equivalence relations."
    applicationTime := .afterCompilation
    add declName stx attrKind := MetaM.run' <| withRef stx <| addQuotifyAttribute declName attrKind
    erase declName := MetaM.run' <| eraseQuotifyAttribute declName
  }
