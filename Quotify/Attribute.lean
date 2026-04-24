module
public import Lean.Meta.Basic
import Quotify.Batteries
public import Quotify.Setoid
public import Quotify.Theorem

open Lean Meta Std

namespace Quotify.Extension

public protected structure Setoid where
  declName : Name
  equiv    : Setoid.Equiv

/--
Constructs a `Setoid` from an `Extension.Setoid` and (what is assumed to be) a matching `BinRel`.
That is, the final `Setoid` has the form `{ r := binRel.expr, iseqv := setoid.equiv.proof }`. If the
`BinRel` is parameterized, the returned `Expr` abstracts over those parameters. That is, we get
`λ a₁ … aₙ => { r := binRel.expr a₁ … aₙ, iseqv := setoid.equiv.proof a₁ … aₙ }`.
-/
def Setoid.instance (setoid : Extension.Setoid) (binRel : BinRel) : MetaM Expr := do
  binRel.telescope fun params rel argType => do
    let lvl ← getLevel argType
    let setoidPrefix := mkApp2 (.const ``_root_.Setoid.mk [lvl]) argType rel
    if params.isEmpty then
      return .app setoidPrefix setoid.equiv.proof
    else
      let iseqv ← instantiateLambda setoid.equiv.proof params
      let setoid := Expr.app setoidPrefix iseqv
      mkLambdaFVars params setoid

public abbrev Theorems := HashMap Theorem.Kind (List Theorem)

namespace Theorems

def singleton (kind : Theorem.Kind) (thm : Theorem) : Theorems :=
  {(kind, [thm])}

def add (thms : Theorems) (kind : Theorem.Kind) (thm : Theorem) : Theorems :=
  thms.alter kind fun thms? =>
    match thms? with
    | none => [thm]
    | some thms => thms.concat thm

def erase (thms : Theorems) (kind : Theorem.Kind) (thm : Theorem) : Theorems :=
  thms.alter kind fun thms? =>
    match thms? with
    | none => none
    | some thms => thms.erase thm

def merge (thms₁ thms₂ : Theorems) : Theorems :=
  thms₁.mergeWith (fun _ => List.append) thms₂

public instance : ToMessageData Theorems where
  toMessageData thms := Id.run do
    let mut msg : MessageData := .nil
    for (kind, thms) in thms do
      let thmNames := thms.map (MessageData.ofConstName ·.declName)
      msg := msg ++ m!"• {kind}: {thmNames}\n"
    return msg

end Theorems

public inductive Entry.Val where
  | setoid (s : Extension.Setoid)
  | theorem (kind : Theorem.Kind) (thm : Theorem)
  deriving Inhabited

public structure Entry.Item where
  key : BinRel
  val : Val
  deriving Inhabited

public inductive Entry.Op where
  | add
  | erase
  deriving Inhabited

public structure Entry extends Entry.Item where
  op : Entry.Op
  deriving Inhabited

public structure Info where
  setoid?  : Option Extension.Setoid := none
  theorems : Theorems                := ∅

public abbrev Infos := HashMap BinRel Info

namespace Infos

def addItem (infos : Infos) (item : Entry.Item) : Infos :=
  infos.alter item.key fun info? =>
    match info?, item.val with
    | none,      .setoid s         => some { setoid? := s }
    | none,      .theorem kind thm => some { theorems := .singleton kind thm }
    | some info, .setoid s         => some { info with setoid? := s }
    | some info, .theorem kind thm => some { info with theorems := info.theorems.add kind thm }

def eraseItem (infos : Infos) (item : Entry.Item) : Infos :=
  infos.alter item.key fun info? =>
    match info?, item.val with
    | none,      _                 => none
    | some info, .setoid _         => some { info with setoid? := none }
    | some info, .theorem kind thm => some { info with theorems := info.theorems.erase kind thm }

def addEntry (infos : Infos) (entry : Entry) : Infos :=
  match entry.op with
  | .add   => infos.addItem entry.toItem
  | .erase => infos.eraseItem entry.toItem

public def getMatchingSetoid? (infos : Infos) (binRel : BinRel) : MetaM (Option Extension.Setoid) := do
  for (pattern, info) in infos do
    let some setoid := info.setoid? | continue
    let some mat ← pattern.match? binRel | continue
    let equiv ← instantiateMatch mat setoid.equiv
    return some { setoid with equiv }
  return none
where
  instantiateMatch (mat : BinRel.Match) (equiv : Setoid.Equiv) : MetaM Setoid.Equiv := do
    let proof ← instantiateLambda equiv.proof mat.params
    -- If `mat` was obtained by matching a target which is not fully applied, then `params` will
    -- contain mvars for those arguments which are to remain abstracted. Thus, after instantiating
    -- `mat.params`, we abstract these mvars again.
    let mvarParams := mat.params.filter (·.isMVar)
    let proof ← mkLambdaFVars mvarParams proof
    -- As we keep an `Equiv` abstracted over the same level parameters as its corresponding
    -- `BinRel`, the `equiv.levelParams` should match up with `pattern.levelParams`, which matches
    -- up with `mat.levels`.
    let proof := proof.instantiateLevelParams equiv.levelParams mat.levels
    -- The `Equiv`'s new level params are those of the matched `BinRel`.
    let levelParams := binRel.levelParams
    return { proof, levelParams }

public def getMatchingSetoidInstance? (infos : Infos) (binRel : BinRel) : MetaM (Option Expr) := do
  let some setoid ← getMatchingSetoid? infos binRel | return none
  setoid.instance binRel

public def getMatchingTheorems (infos : Infos) (binRel : BinRel) : MetaM Theorems := do
  let mut thms : Theorems := ∅
  for (pattern, info) in infos do
    unless (← pattern.match? binRel).isSome do continue
    thms := thms.merge info.theorems
  return thms

/--
Like `getMatchingTheorems`, but instantiates the resulting theorems with the `Match` against the
given `BinRel`.
-/
public def getMatchingTheorems' (infos : Infos) (binRel : BinRel) : MetaM Theorems := do
  let mut thms : Theorems := ∅
  for (pattern, info) in infos do
    let some mat ← pattern.match? binRel | continue
    for (kind, ts) in info.theorems do
      for thm in ts do
        let instantiatedThm ← instantiateMatch mat thm
        thms := thms.add kind instantiatedThm
  return thms
where
  instantiateMatch (mat : BinRel.Match) (thm : Theorem) : MetaM Theorem := do
    let fn ← instantiateLambda thm.fn mat.params
    -- If `mat` was obtained by matching a target which is not fully applied, then `params` will
    -- contain mvars for those arguments which are to remain abstracted. Thus, after instantiating
    -- `mat.params`, we abstract these mvars again.
    let mvarParams := mat.params.filter (·.isMVar)
    let fn ← mkLambdaFVars mvarParams fn
    -- As we keep a `Theorem` abstracted over the same level parameters as its corresponding
    -- `BinRel`, the `thm.levelParams` should match up with `pattern.levelParams`, which matches
    -- up with `mat.levels`.
    let fn := fn.instantiateLevelParams thm.levelParams mat.levels
    -- The `Theorem`'s new level params are those of the matched `BinRel`.
    let levelParams := binRel.levelParams
    return { declName := thm.declName, fn, numParams := mvarParams.size, levelParams }

end Extension.Infos

open Extension

public abbrev Extension := SimpleScopedEnvExtension Entry Infos

namespace Extension

def mk : IO Extension :=
  registerSimpleScopedEnvExtension {
    initial  := ∅
    addEntry := Infos.addEntry
  }

public def infos (ex : Extension) : MetaM Infos := do
  let env ← getEnv
  return ex.getState env

public def getMatchingSetoid? (ex : Extension) (binRel : BinRel) : MetaM (Option Extension.Setoid) := do
  let info ← ex.infos
  info.getMatchingSetoid? binRel

public def getMatchingSetoidInstance? (ex : Extension) (binRel : BinRel) : MetaM (Option Expr) := do
  let info ← ex.infos
  info.getMatchingSetoidInstance? binRel

public def getMatchingTheorems (ex : Extension) (binRel : BinRel) : MetaM Theorems := do
  let info ← ex.infos
  info.getMatchingTheorems binRel

public def getMatchingTheorems' (ex : Extension) (binRel : BinRel) : MetaM Theorems := do
  let info ← ex.infos
  info.getMatchingTheorems' binRel

end Extension

public initialize extension : Extension ← Extension.mk

namespace Attribute

inductive Target.Val where
  | setoid (declName : Name) (equiv : Setoid.Equiv)
  | theorem (kind : Theorem.Kind) (thm : Theorem)

structure Target where
  binRel : BinRel
  val    : Target.Val

def Target.forDecl (declName : Name) : MetaM Target := do
  match ← getConstInfo declName with
  | .defnInfo defInfo =>
    let some setoid ← Setoid.forDef? defInfo
      | throwError "You can only use the `[quotify]` attribute on definitions of \
                    `{.ofConstName ``Setoid}`s."
    let some (binRel, equiv) ← setoid.components?
      | throwError "`quotify` failed to extract the relation from the `{.ofConstName ``Setoid} \
                    `{.ofConstName declName}"
    return { binRel, val := .setoid declName equiv }
  | .thmInfo thmInfo =>
    let some (thm, kind, binRel) ← Theorem.forThm? thmInfo
      | throwError "Theorems marked with `[quotify]` must have one of the following forms:\n\n\
                      • `∀ …, ∀ a b, (a ≈ b) → f a = f b`\n\
                      • `∀ …, ∀ a₁ b₁ a₂ b₂, (a₁ ≈ a₂) → (b₁ ≈ b₂) → f a₁ b₁ = f a₂ b₂`\n\
                      • `∀ …, ∀ a b, (a ≈ b) → f a ≈ f b`\n\
                      • `∀ …, ∀ a₁ a₂, (a₁ ≈ a₂) → ∀ b₁ b₂, (b₁ ≈ b₂) → f a₁ b₁ ≈ f a₂ b₂`\n\n\
                    The given theorem does not match any of these."
    return { binRel, val := .theorem kind thm }
  | _ =>
    throwError "You can only use the `[quotify]` attribute on theorems or definitions, but \
                `{.ofConstName declName}` is neither."

end Attribute

open Attribute

def Extension.addTarget (ex : Extension) (tgt : Target) (attrKind : AttributeKind) : MetaM Unit :=
  match tgt.val with
  | .theorem kind thm =>
    let entry := { key := tgt.binRel, op := .add, val := .theorem kind thm }
    ex.add entry attrKind
  | .setoid declName equiv => do
    let infos ← extension.infos
    if let some setoid ← infos.getMatchingSetoid? tgt.binRel then
      throwError "The relation {indentExpr tgt.binRel.expr}\nis already covered by the \
                  `{.ofConstName ``Setoid}` `{.ofConstName setoid.declName}` marked with \
                  `[quotify]`."
    let setoid := { declName, equiv }
    let entry := { key := tgt.binRel, op := .add, val := .setoid setoid }
    ex.add entry attrKind

def Extension.eraseTarget (ex : Extension) (tgt : Target) : MetaM Unit :=
  match tgt.val with
  | .theorem kind thm =>
    -- The value of `thm` is irrelevant here. The `kind` could be as well, but it simplifies our
    -- search for the theorem to delete.
    let entry := { key := tgt.binRel, op := .erase, val := .theorem kind thm }
    ex.add entry
  | .setoid declName equiv =>
    -- The value of `setoid` is irrelevant here.
    let setoid := { declName, equiv }
    let entry := { key := tgt.binRel, op := .erase, val := .setoid setoid }
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
