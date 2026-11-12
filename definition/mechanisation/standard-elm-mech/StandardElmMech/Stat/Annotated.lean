/-
  A Standard Definition of Elm? Mechanisation: annotated phrases and the checker, plan step 9
  (section 7, decision D10).

  An annotated phrase is a bare phrase with the semantic objects of a derivation's sentences: the
  type at each leaf and binder (a constant, an occurrence, `[]`, a pattern variable, a wildcard, a
  record pattern), the instance (the types for the scheme's bound variables) at each occurrence of
  a variable, constructor or operator, the group's value environment before closure at each
  declaration, U' at each annotated binding, and, in modules, the type environment of the type
  declarations (with its generated type names), the split of `r_sm_topdec_seq_types`, and the U
  of each port. The other types (of applications, lambdas, tuples, matches, rows and value
  environments of patterns) are computed from the nodes (`ty`, `ve`, `row`), so a certificate
  stores only what a derivation chooses. Imports, headers, type expressions and type declarations
  given their names are computed by Deterministic.lean.

  `checkExp C a` checks at each node the premises of the one rule whose conclusion has the node's
  form; it is structurally recursive, so `decide +kernel` runs it. CheckSound.lean proves it sound.
-/
import StandardElmMech.Stat.Deterministic

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

/-! ## Annotated patterns -/

mutual
inductive AAtPat where
  | wild (τ : Ty)
  | scon (sc : SLit) (τ : Ty)
  | var (x : Var) (τ : Ty)
  | con (lc : LongId) (inst : List Ty) (τ : Ty)
  | unit
  | tuple (p1 p2 : APat) (p3 : Option APat)
  | nil (τ : Ty)
  | record (row : Option APatRow) (τ : Ty)
  | paren (p : APat)
inductive APatRow where
  | field (l : Lab) (τ : Ty) (rest : Option APatRow)
inductive APat where
  | atpat (a : AAtPat)
  | con (lc : LongId) (inst : List Ty) (args : List AAtPat) (τ : Ty)
  | cons (p1 p2 : APat)
  | as (p : APat) (x : Var)
end

instance : Inhabited APat := ⟨.atpat .unit⟩
instance : Inhabited AAtPat := ⟨.unit⟩

mutual
def AAtPat.erase : AAtPat → BAtPat
  | .wild _ => .wild
  | .scon sc _ => .scon sc
  | .var x _ => .var x
  | .con lc _ _ => .con lc
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (APat.erase p1) (APat.erase p2) (APat.eraseOpt p3)
  | .nil _ => .nil
  | .record row _ => .record (APatRow.eraseOpt row)
  | .paren p => .paren (APat.erase p)
def APatRow.erase : APatRow → BPatRow
  | .field l _ rest => .field l (APatRow.eraseOpt rest)
def APatRow.eraseOpt : Option APatRow → Option BPatRow
  | none => none
  | some r => some (APatRow.erase r)
def APat.erase : APat → BPat
  | .atpat a => .atpat (AAtPat.erase a)
  | .con lc _ args _ => .con lc (AAtPat.eraseList args)
  | .cons p1 p2 => .cons (APat.erase p1) (APat.erase p2)
  | .as p x => .as (APat.erase p) x
def APat.eraseOpt : Option APat → Option BPat
  | none => none
  | some p => some (APat.erase p)
def AAtPat.eraseList : List AAtPat → List BAtPat
  | [] => []
  | a :: as => AAtPat.erase a :: AAtPat.eraseList as
end

mutual
def AAtPat.ty : AAtPat → Ty
  | .wild τ | .scon _ τ | .var _ τ | .con _ _ τ | .nil τ | .record _ τ => τ
  | .unit => tUnitTy
  | .tuple p1 p2 p3 => tupleTy (APat.ty p1) (APat.ty p2) (APat.tyOpt p3)
  | .paren p => APat.ty p
def APat.ty : APat → Ty
  | .atpat a => AAtPat.ty a
  | .con _ _ _ τ => τ
  | .cons p1 _ => listTy (APat.ty p1)
  | .as p _ => APat.ty p
def APat.tyOpt : Option APat → Option Ty
  | none => none
  | some p => some (APat.ty p)
end

def AAtPat.tyList : List AAtPat → List Ty
  | [] => []
  | a :: as => a.ty :: AAtPat.tyList as

mutual
def AAtPat.ve : AAtPat → ValEnv
  | .var x τ => [(x, (mono τ, .v))]
  | .tuple p1 p2 p3 => FMap.modify (FMap.modify (APat.ve p1) (APat.ve p2)) (APat.veOpt p3)
  | .record row _ => APatRow.veOpt row
  | .paren p => APat.ve p
  | _ => []
def APatRow.ve : APatRow → ValEnv
  | .field l τ rest => FMap.modify [(l, (mono τ, .v))] (APatRow.veOpt rest)
def APatRow.veOpt : Option APatRow → ValEnv
  | none => []
  | some r => APatRow.ve r
def APat.ve : APat → ValEnv
  | .atpat a => AAtPat.ve a
  | .con _ _ args _ => FMap.plusAll (AAtPat.veList args)
  | .cons p1 p2 => FMap.modify (APat.ve p1) (APat.ve p2)
  | .as p x => FMap.modify (APat.ve p) [(x, (mono (APat.ty p), .v))]
def APat.veOpt : Option APat → ValEnv
  | none => []
  | some p => APat.ve p
def AAtPat.veList : List AAtPat → List ValEnv
  | [] => []
  | a :: as => AAtPat.ve a :: AAtPat.veList as
end

mutual
def APatRow.row : APatRow → Row
  | .field l τ rest => Row.modify [(l, τ)] (APatRow.rowOpt rest)
def APatRow.rowOpt : Option APatRow → Row
  | none => []
  | some r => APatRow.row r
end

/-! ## Annotated expressions -/

mutual
inductive AAtExp where
  | scon (sc : SLit) (τ : Ty)
  | var (lv : LongId) (inst : List Ty) (τ : Ty)
  | con (lc : LongId) (inst : List Ty) (τ : Ty)
  | op (o : Op) (inst : List Ty) (τ : Ty)
  | unit
  | tuple (e1 e2 : AExp) (e3 : Option AExp)
  | nil (τ : Ty)
  | record (row : Option AExpRow)
  | update (x : Var) (inst : List Ty) (τ : Ty) (row : AExpRow)
  | letE (d : ADec) (e : AExp)
  | paren (e : AExp)
inductive AExpRow where
  | field (l : Lab) (e : AExp) (rest : Option AExpRow)
inductive AExp where
  | atexp (a : AAtExp)
  | app (e : AExp) (a : AAtExp)
  | lam (p : AAtPat) (e : AExp)
  | caseE (e : AExp) (m : AMatch)
inductive AMatch where
  | mk (mr : AMRule) (rest : Option AMatch)
inductive AMRule where
  | mk (p : APat) (e : AExp)
/-- A declaration: the group's value environment before closure, and its bindings. -/
inductive ADec where
  | val (VE : ValEnv) (vb : AValBind)
/-- `ann`: the annotation and its U'. -/
inductive AValBind where
  | var (x : Var) (ann : Option (BTy × List BVar)) (τ : Ty) (e : AExp) (rest : Option AValBind)
  | pat (p : AAtPat) (e : AExp)
end

instance : Inhabited AExp := ⟨.atexp .unit⟩
instance : Inhabited AAtExp := ⟨.unit⟩

mutual
def AAtExp.erase : AAtExp → BAtExp
  | .scon sc _ => .scon sc
  | .var lv _ _ => .var lv
  | .con lc _ _ => .con lc
  | .op o _ _ => .op o
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (AExp.erase e1) (AExp.erase e2) (AExp.eraseOpt e3)
  | .nil _ => .nil
  | .record row => .record (AExpRow.eraseOpt row)
  | .update x _ _ row => .update x (AExpRow.erase row)
  | .letE d e => .letE (ADec.erase d) (AExp.erase e)
  | .paren e => .paren (AExp.erase e)
def AExpRow.erase : AExpRow → BExpRow
  | .field l e rest => .field l (AExp.erase e) (AExpRow.eraseOpt rest)
def AExpRow.eraseOpt : Option AExpRow → Option BExpRow
  | none => none
  | some r => some (AExpRow.erase r)
def AExp.erase : AExp → BExp
  | .atexp a => .atexp (AAtExp.erase a)
  | .app e a => .app (AExp.erase e) (AAtExp.erase a)
  | .lam p e => .lam p.erase (AExp.erase e)
  | .caseE e m => .caseE (AExp.erase e) (AMatch.erase m)
def AExp.eraseOpt : Option AExp → Option BExp
  | none => none
  | some e => some (AExp.erase e)
def AMatch.erase : AMatch → BMatch
  | .mk mr rest => .mk (AMRule.erase mr) (AMatch.eraseOpt rest)
def AMatch.eraseOpt : Option AMatch → Option BMatch
  | none => none
  | some m => some (AMatch.erase m)
def AMRule.erase : AMRule → BMRule
  | .mk p e => .mk p.erase (AExp.erase e)
def ADec.erase : ADec → BDec
  | .val _ vb => .val (AValBind.erase vb)
def AValBind.erase : AValBind → BValBind
  | .var x ann _ e rest => .var x (ann.map Prod.fst) (AExp.erase e) (AValBind.eraseOpt rest)
  | .pat p e => .pat p.erase (AExp.erase e)
def AValBind.eraseOpt : Option AValBind → Option BValBind
  | none => none
  | some vb => some (AValBind.erase vb)
end

/-- The codomain of a function type. -/
def Ty.cod : Ty → Ty
  | .fn _ τ => τ
  | τ => τ

mutual
def AAtExp.ty : AAtExp → Ty
  | .scon _ τ | .var _ _ τ | .con _ _ τ | .op _ _ τ | .nil τ | .update _ _ τ _ => τ
  | .unit => tUnitTy
  | .tuple e1 e2 e3 => tupleTy (AExp.ty e1) (AExp.ty e2) (AExp.tyOpt e3)
  | .record row => .record (AExpRow.rowOpt row) none
  | .letE _ e => AExp.ty e
  | .paren e => AExp.ty e
def AExpRow.row : AExpRow → Row
  | .field l e rest => Row.modify [(l, AExp.ty e)] (AExpRow.rowOpt rest)
def AExpRow.rowOpt : Option AExpRow → Row
  | none => []
  | some r => AExpRow.row r
def AExp.ty : AExp → Ty
  | .atexp a => AAtExp.ty a
  | .app e _ => (AExp.ty e).cod
  | .lam p e => .fn p.ty (AExp.ty e)
  | .caseE _ m => (AMatch.ty m).cod
def AExp.tyOpt : Option AExp → Option Ty
  | none => none
  | some e => some (AExp.ty e)
def AMatch.ty : AMatch → Ty
  | .mk mr _ => AMRule.ty mr
def AMRule.ty : AMRule → Ty
  | .mk p e => .fn p.ty (AExp.ty e)
end

def annU : Option (BTy × List BVar) → List BVar
  | none => []
  | some (_, U') => U'

/-- The value environment a value binding gives (its conclusion in r:s-valbind-var and r:s-valbind-pat). -/
def AValBind.ve : AValBind → ValEnv
  | .var x ann τ _ rest =>
    FMap.modify [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, .v))]
      (match rest with
       | none => []
       | some vb => AValBind.ve vb)
  | .pat p _ => p.ve

def AValBind.veOpt : Option AValBind → ValEnv
  | none => []
  | some vb => vb.ve

/-- What r:s-dec-group gives: the group's environment, closed. -/
def ADec.result (C : Ctx) : ADec → ValEnv
  | .val VE _ => closGroup C.tyvars VE

/-! ## The checker -/

/-- The instance a constant records: its type, for an integer constant (∀α.α). -/
def litInst (sc : SLit) (τ : Ty) : List Ty :=
  match sc with
  | .int _ => [τ]
  | _ => []

def isConTy : Ty → Bool
  | .con _ _ => true
  | _ => false

def isListTy : Ty → Bool
  | .con [_] t => t == tList
  | _ => false

def isRecordTy : Ty → Bool
  | .record _ _ => true
  | _ => false

def recordRow : Ty → Row
  | .record ρ _ => ρ
  | _ => []

mutual
def checkAtPat (C : Ctx) : AAtPat → Bool
  | .wild _ => true
  | .scon sc τ => genAt (typeOf sc) (litInst sc τ) τ && decide (τ ∈ [tIntTy, tCharTy, tStringTy])
  | .var _ _ => true
  | .con lc inst τ =>
    match C.lookupVal lc with
    | some (σ, .c) => genAt σ inst τ && isConTy τ
    | _ => false
  | .unit => true
  | .tuple p1 p2 p3 => checkPat C p1 && checkPat C p2 && checkPatOpt C p3
  | .nil τ => isListTy τ
  | .record row τ => checkPatRowOpt C row && isRecordTy τ && (Row.subB (APatRow.rowOpt row) (recordRow τ))
  | .paren p => checkPat C p
def checkPatRow (C : Ctx) : APatRow → Bool
  | .field _ _ rest => checkPatRowOpt C rest
def checkPatRowOpt (C : Ctx) : Option APatRow → Bool
  | none => true
  | some r => checkPatRow C r
def checkPat (C : Ctx) : APat → Bool
  | .atpat a => checkAtPat C a
  | .con lc inst args τ =>
    (match C.lookupVal lc with
     | some (σ, .c) => genAt σ inst (arrows (AAtPat.tyList args) τ) && isConTy τ
     | _ => false) && checkAtPatList C args
  | .cons p1 p2 => checkPat C p1 && checkPat C p2 && decide (APat.ty p2 = listTy (APat.ty p1))
  | .as p _ => checkPat C p
def checkPatOpt (C : Ctx) : Option APat → Bool
  | none => true
  | some p => checkPat C p
def checkAtPatList (C : Ctx) : List AAtPat → Bool
  | [] => true
  | a :: as => checkAtPat C a && checkAtPatList C as
end

/-- The first option of r:s-valbind-var. -/
def checkAnn (C : Ctx) : Option (BTy × List BVar) → Ty → Bool
  | none, _ => true
  | some (ty, U'), τ =>
    newForB U' ty C.U && decide (elabTy (C.plusU U') ty = some τ) && U'.all (fun v => !decide (v ∈ C.tyvars))

mutual
def checkAtExp (C : Ctx) : AAtExp → Bool
  | .scon sc τ => genAt (typeOf sc) (litInst sc τ) τ
  | .var lv inst τ =>
    match C.lookupVal lv with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .con lc inst τ =>
    match C.lookupVal lc with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .op o inst τ =>
    match OTstat o with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .unit => true
  | .tuple e1 e2 e3 => checkExp C e1 && checkExp C e2 && checkExpOpt C e3
  | .nil τ => isListTy τ
  | .record row => checkExpRowOpt C row
  | .update x inst τ row =>
    (match C.lookupVal ⟨none, x⟩ with
     | some (σ, _) => genAt σ inst τ
     | none => false) &&
    isRecordTy τ && checkExpRow C row && Row.subB (AExpRow.row row) (recordRow τ)
  | .letE d e => checkDec C d && checkExp (C.plusVE (d.result C)) e
  | .paren e => checkExp C e
def checkExpRow (C : Ctx) : AExpRow → Bool
  | .field _ e rest => checkExp C e && checkExpRowOpt C rest
def checkExpRowOpt (C : Ctx) : Option AExpRow → Bool
  | none => true
  | some r => checkExpRow C r
def checkExp (C : Ctx) : AExp → Bool
  | .atexp a => checkAtExp C a
  | .app e a =>
    checkExp C e && checkAtExp C a &&
      (match AExp.ty e with
       | .fn τ' _ => decide (τ' = AAtExp.ty a)
       | _ => false)
  | .lam p e => checkAtPat C p && checkExp (C.plusVE p.ve) e
  | .caseE e m =>
    checkExp C e && checkMatch C m &&
      (match AMatch.ty m with
       | .fn τ _ => decide (τ = AExp.ty e)
       | _ => false)
def checkExpOpt (C : Ctx) : Option AExp → Bool
  | none => true
  | some e => checkExp C e
def checkMatch (C : Ctx) : AMatch → Bool
  | .mk mr rest => checkMRule C mr && checkMatchOptAt C (AMRule.ty mr) rest
/-- The rest of a match, every rule at type τ. -/
def checkMatchOptAt (C : Ctx) (τ : Ty) : Option AMatch → Bool
  | none => true
  | some m => checkMatch C m && decide (AMatch.ty m = τ)
def checkMRule (C : Ctx) : AMRule → Bool
  | .mk p e => checkPat C p && checkExp (C.plusVE p.ve) e
def checkDec (C : Ctx) : ADec → Bool
  | .val VE vb => checkValBind (C.plusVE VE) vb && decide (vb.ve = VE)
def checkValBind (C : Ctx) : AValBind → Bool
  | .var _ ann τ e rest =>
    checkAnn C ann τ && checkExp (C.plusU (annU ann)) e && decide (AExp.ty e = τ) && checkValBindOpt C rest
  | .pat p e => checkAtPat C p && checkExp C e && decide (AExp.ty e = p.ty)
def checkValBindOpt (C : Ctx) : Option AValBind → Bool
  | none => true
  | some vb => checkValBind C vb
end

/-! ## Modules -/

inductive ATopDec where
  | value (VE : ValEnv) (vb : AValBind)
  | types (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind)
  /-- r_sm_topdec_seq_types: the phrase split at a separator. -/
  | typesSplit (a1 a2 : ATopDec)
  | port (x : Var) (ty : BTy) (U : List BVar)
  | seq (a1 a2 : ATopDec)

def ATopDec.erase : ATopDec → BTopDec
  | .value _ vb => .value vb.erase
  | .types _ _ db tbs => .types db tbs
  | .typesSplit a1 a2 =>
    match ATopDec.erase a1, ATopDec.erase a2 with
    | .types db tbs1, .types _ tbs2 => .types db (tbs1 ++ tbs2)
    | d, _ => d
  | .port x ty _ => .port x ty
  | .seq a1 a2 => .seq (ATopDec.erase a1) (ATopDec.erase a2)

structure AModule where
  header : BHeader
  imports : List BImport
  body : Option ATopDec

abbrev AProgram := List AModule

def AModule.erase (a : AModule) : BModule := ⟨a.header, a.imports, a.body.map ATopDec.erase⟩

/-- A type-declaration phrase that r:sm-topdec-seq may split there: its two parts. -/
def splitShape : BTopDec → BTopDec → Bool
  | .types db tbs1, .types none tbs2 => (db.isSome || !tbs1.isEmpty) && !tbs2.isEmpty
  | _, _ => false

def checkTopDec (C : Ctx) : ATopDec → Option (Env × PortEnv)
  | .value VE vb =>
    if checkValBind (C.plusVE VE) vb && decide (vb.ve = VE) then
      some (Env.ofVE (closGroup C.tyvars VE), [])
    else none
  | .types TE VE db tbs => if checkTypes C TE VE db tbs then some (⟨[], TE, VE⟩, []) else none
  | .typesSplit a1 a2 =>
    if splitShape a1.erase a2.erase then
      match checkTopDec C a1 with
      | some (E1, PE1) =>
        match checkTopDec (C.oplusE E1) a2 with
        | some (E2, PE2) => some (E1.plus E2, Env.plusPE PE1 PE2)
        | none => none
      | none => none
    else none
  | .port x ty U => elabPort C x ty U
  | .seq a1 a2 =>
    match checkTopDec C a1 with
    | some (E1, PE1) =>
      match checkTopDec (C.oplusE E1) a2 with
      | some (E2, PE2) => some (E1.plus E2, Env.plusPE PE1 PE2)
      | none => none
    | none => none

def checkTopDecOpt (C : Ctx) : Option ATopDec → Option (Env × PortEnv)
  | none => some (Env.empty, [])
  | some d => checkTopDec C d

/-- The context r:sm-module elaborates a module's declarations in. -/
def modCtx (B : SBasis) (π : ProvMap) : Ctx := ⟨B.T, [], envOf B.ME π⟩

/-- The context of a module's declarations, from its imports read after the default ones. -/
def importCtx (B : SBasis) (imps : List BImport) : Option Ctx :=
  (elabImports B π0 (defaultImports ++ imps)).map (modCtx B)

/-- What r:sm-module gives in the context C of the module's imports, when the certificate checks. -/
def AModule.resultIn (B : SBasis) (C : Ctx) (a : AModule) : Option (SBasis × Env) :=
  match checkTopDecOpt C a.body with
  | none => none
  | some (E, PE) =>
    match expose E a.header.exposing with
    | none => none
    | some I =>
      if a.header.name ∈ B.ME.keys then none
      else some (⟨diffL (dedupL E.tynames) B.T, [(a.header.name, I)], PE⟩, E)

/-- What r:sm-module gives, when the certificate checks: B' and E. -/
def AModule.result (B : SBasis) (a : AModule) : Option (SBasis × Env) :=
  match importCtx B a.imports with
  | none => none
  | some C => a.resultIn B C

theorem AModule.result_of_ctx {B : SBasis} {a : AModule} {C : Ctx} (h : importCtx B a.imports = some C) :
    a.result B = a.resultIn B C := by
  simp only [AModule.result, h]

def checkModule (B : SBasis) (a : AModule) : Bool := (a.result B).isSome

/-- The bases of r:p-stat-module: B₁ = B, B_{i+1} = B_i + B'_i; none when a module does not check. -/
def AProgram.bases (B : SBasis) : AProgram → Option (List SBasis)
  | [] => some []
  | a :: rest =>
    match a.result B with
    | some (B', _) => (AProgram.bases (B.plus B') rest).map (B :: ·)
    | none => none

/-- Every module checks in the basis the earlier ones build. -/
def checkProgram (B : SBasis) (a : AProgram) : Bool := (AProgram.bases B a).isSome

end StandardElm.Stat
