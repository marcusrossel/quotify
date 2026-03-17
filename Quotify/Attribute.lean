module
public import Lean.Meta.Basic
public import Quotify.Setoid

open Lean Meta Std

namespace Quotify.Extension

public protected structure Setoid where
  declName : Name
  equiv    : Expr

public inductive Entry.Val where
  | setoid (s : Extension.Setoid)
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
  setoid?    : Option Extension.Setoid := none
  compatThms : List Name               := []

def Proofs.equiv? (proofs : Proofs) : Option Expr :=
  Setoid.equiv <$> proofs.setoid?

-- **TODO** The universe levels of the `BinRel`s are normalized, but those of the equivalence proofs
--          are not.
public abbrev Info := HashMap BinRel Proofs

namespace Info

def addItem (info : Info) (item : Entry.Item) : Info :=
  info.alter item.key fun proofs? =>
    match proofs?, item.val with
    | none,        .setoid s     => some { setoid? := s }
    | none,        .theorem name => some { compatThms := [name] }
    | some proofs, .setoid s     => some { proofs with setoid? := s }
    | some proofs, .theorem name => some { proofs with compatThms := proofs.compatThms.concat name }

def eraseItem (info : Info) (item : Entry.Item) : Info :=
  info.alter item.key fun proofs? =>
    match proofs?, item.val with
    | none,        _             => none
    | some proofs, .setoid _     => some { proofs with setoid? := none }
    | some proofs, .theorem name => some { proofs with compatThms := proofs.compatThms.erase name }

def addEntry (info : Info) (entry : Entry) : Info :=
  match entry.kind with
  | .add   => info.addItem entry.toItem
  | .erase => info.eraseItem entry.toItem

public def getMatchingSetoid? (info : Info) (binRel : BinRel) : MetaM (Option Extension.Setoid) := do
  for (pattern, proofs) in info do
    let some setoid := proofs.setoid? | continue
    let some mat ← pattern.match? binRel | continue
    let equiv ← mat.instantiate setoid.equiv
    return some { setoid with equiv }
  return none

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
  | setoid (equiv : Expr)
  | theorem

structure Target where
  binRel   : BinRel
  declName : Name
  val      : Target.Val

def Target.forDecl (declName : Name) : MetaM Target := do
  match ← getConstInfo declName with
  | .defnInfo defInfo =>
    let some setoid ← Setoid.forDef? defInfo
      | throwError "You can only use the `[quotify]` attribute on definitions of \
                    `{.ofConstName ``Setoid}`s."
    let binRel ← setoid.binRel
    let equiv ← setoid.equivProof
    return { binRel, declName, val := .setoid equiv }
  | .thmInfo thmInfo =>
    let some binRel ← BinRel.forThm? thmInfo
      | throwError "You can only use the `[quotify]` attribute on theorems of the form \
                  `∀ … lhs rhs, r … lhs rhs` where `r …` is a homogeneous binary relation."
    return { binRel, declName, val := .theorem }
  | _ => throwError "You can only use the `[quotify]` attribute on theorems or definitions, but \
                     `{.ofConstName declName}` is neither."

end Attribute

open Attribute

def Extension.addTarget (ex : Extension) (tgt : Target) (attrKind : AttributeKind) : MetaM Unit :=
  match tgt.val with
  | .theorem =>
    let entry := { key := tgt.binRel, kind := .add, val := .theorem tgt.declName }
    ex.add entry attrKind
  | .setoid equiv => do
    let info ← extension.info
    if let some setoid ← info.getMatchingSetoid? tgt.binRel then
      throwError "The relation {indentExpr tgt.binRel.expr}\nis already covered by the \
                  `{.ofConstName ``Setoid}` `{.ofConstName setoid.declName}` marked with \
                  `[quotify]`."
    let setoid := { declName := tgt.declName, equiv }
    let entry := { key := tgt.binRel, kind := .add, val := .setoid setoid }
    ex.add entry attrKind

def Extension.eraseTarget (ex : Extension) (tgt : Target) : MetaM Unit :=
  match tgt.val with
  | .theorem =>
    let entry := { key := tgt.binRel, kind := .erase, val := .theorem tgt.declName }
    ex.add entry
  | .setoid equiv =>
    -- The value of `setoid` is irrelevant here.
    let setoid := { declName := tgt.declName, equiv }
    let entry := { key := tgt.binRel, kind := .erase, val := .setoid setoid }
    ex.add entry

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
