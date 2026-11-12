/-
  A Standard Definition of Elm? Mechanisation: an inference for the static semantics, written in
  Lean and not proved, plan step 9 (section 11). Algorithm W over the bare syntax with classes
  (B3), rows (A23), rigid explicit variables (G2-5), groups monomorphic within themselves and
  closed with A93's extra variables (G2-6), and the type declarations of a module solved in
  Appendix A's order (B5). It returns annotated phrases with inference variables, then applies the
  final substitution to them. The checker decides whether the result is a derivation.
-/
import StandardElmMech.Stat.Unify

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule BProgram)

/-! ## Helpers -/

mutual
/-- The labels of the records whose tail is `e`. -/
def tailLabels (e : RowVar) : Ty → List Lab
  | .var _ => []
  | .record ρ tl => (if tl = some e then ρ.map (·.1) else []) ++ tailLabelsRow e ρ
  | .fn a b => tailLabels e a ++ tailLabels e b
  | .con as _ => tailLabelsList e as
def tailLabelsRow (e : RowVar) : Row → List Lab
  | [] => []
  | (_, τ) :: rest => tailLabels e τ ++ tailLabelsRow e rest
def tailLabelsList (e : RowVar) : List Ty → List Lab
  | [] => []
  | τ :: rest => tailLabels e τ ++ tailLabelsList e rest
end

/-- An instance of σ with new inference variables: the instance list and the type. -/
def instantiate (σ : Scheme) : Inf (List Ty × Ty) := do
  let ts ← σ.bound.mapM fun v => match v with
    | .ty a => freshTy a.cls
    | .row e => do
      let r ← freshRow (tailLabels e σ.body)
      return Ty.record [] (some r)
  match bindSubst σ.bound ts with
  | some S =>
    match S.apply σ.body with
    | some τ => return (ts, τ)
    | none => throw "instantiate"
  | none => throw "instantiate"

def lookupInst (C : Ctx) (lv : LongId) : Inf (List Ty × Ty) := do
  match C.lookupVal lv with
  | some (σ, _) => instantiate σ
  | none => throw s!"unbound: {repr lv}"

/-- The explicit variables an annotation makes new (G2-5): its names not explicit in C, each a row
    variable if used as an extension variable, a type variable otherwise. -/
def annVars (CU : List BVar) (ty : BTy) : List BVar :=
  seqVars ((dedupL (bTyNames ty)).filter fun s => s ∉ namesU CU) (bTyExtNames ty)

def zonkVE (s : InfState) (VE : ValEnv) : ValEnv :=
  VE.mapV fun p => (⟨p.1.bound, zonk s fuel0 p.1.body⟩, p.2)

def zonkCtx (s : InfState) (C : Ctx) : Ctx :=
  { C with E := { C.E with VE := zonkVE s C.E.VE } }

/-! ## Expressions and patterns -/

mutual
def inferAtPat : Nat → Ctx → BAtPat → Inf AAtPat
  | 0, _, _ => throw "fuel"
  | f + 1, C, p =>
    match p with
    | .wild => return .wild (← freshTy .any)
    | .scon sc =>
      match sc with
      | .int _ => return .scon sc tIntTy
      | .char _ => return .scon sc tCharTy
      | .str _ => return .scon sc tStringTy
      | .float _ _ => throw "float pattern"
    | .var x => return .var x (← freshTy .any)
    | .con lc =>
      match C.lookupVal lc with
      | some (σ, .c) => do
        let (ts, τ) ← instantiate σ
        match τ with
        | .con _ _ => return .con lc ts τ
        | _ => throw "constructor without its arguments"
      | _ => throw s!"not a constructor: {repr lc}"
    | .unit => return .unit
    | .tuple p1 p2 p3 => do
      let a1 ← inferPat f C p1
      let a2 ← inferPat f C p2
      let a3 ← match p3 with
        | none => pure none
        | some p => some <$> inferPat f C p
      return .tuple a1 a2 a3
    | .nil => return .nil (listTy (← freshTy .any))
    | .record row => do
      let arow ← match row with
        | none => pure none
        | some r => some <$> inferPatRow f r
      let ρ := APatRow.rowOpt arow
      let e ← freshRow (ρ.map (·.1))
      return .record arow (.record ρ (some e))
    | .paren p => return .paren (← inferPat f C p)
def inferPatRow : Nat → BPatRow → Inf APatRow
  | 0, _ => throw "fuel"
  | f + 1, .field l rest => do
    let τ ← freshTy .any
    let arest ← match rest with
      | none => pure none
      | some r => some <$> inferPatRow f r
    return .field l τ arest
def inferPat : Nat → Ctx → BPat → Inf APat
  | 0, _, _ => throw "fuel"
  | f + 1, C, p =>
    match p with
    | .atpat a => return .atpat (← inferAtPat f C a)
    | .con lc args =>
      match C.lookupVal lc with
      | some (σ, .c) => do
        let (ts, τc) ← instantiate σ
        let aargs ← inferAtPats f C args
        let β ← freshTy .any
        unifyM τc (arrows (AAtPat.tyList aargs) β)
        return .con lc ts aargs β
      | _ => throw s!"not a constructor: {repr lc}"
    | .cons p1 p2 => do
      let a1 ← inferPat f C p1
      let a2 ← inferPat f C p2
      unifyM a2.ty (listTy a1.ty)
      return .cons a1 a2
    | .as p x => return .as (← inferPat f C p) x
def inferAtPats : Nat → Ctx → List BAtPat → Inf (List AAtPat)
  | 0, _, _ => throw "fuel"
  | _ + 1, _, [] => return []
  | f + 1, C, a :: as => do
    let x ← inferAtPat f C a
    let xs ← inferAtPats f C as
    return x :: xs
end

/-- The members of a group of value bindings joined by `and`. -/
def groupMembers : BValBind → List (Var × Option BTy × BExp)
  | .var x ann e rest =>
    (x, ann, e) :: (match rest with
      | none => []
      | some vb => groupMembers vb)
  | .pat _ _ => []

def buildVarBind : List (Var × Option (BTy × List BVar) × Ty × AExp) → Option AValBind
  | [] => none
  | (x, ann, τ, ae) :: rest => some (.var x ann τ ae (buildVarBind rest))

mutual
def inferAtExp : Nat → Ctx → BAtExp → Inf (AAtExp × Ty)
  | 0, _, _ => throw "fuel"
  | f + 1, C, a =>
    match a with
    | .scon sc =>
      match sc with
      | .int _ => do let α ← freshTy .num; return (.scon sc α, α)
      | .float _ _ => return (.scon sc tFloatTy, tFloatTy)
      | .char _ => return (.scon sc tCharTy, tCharTy)
      | .str _ => return (.scon sc tStringTy, tStringTy)
    | .var lv => do let (ts, τ) ← lookupInst C lv; return (.var lv ts τ, τ)
    | .con lc => do let (ts, τ) ← lookupInst C lc; return (.con lc ts τ, τ)
    | .op o =>
      match OTstat o with
      | some (σ, _) => do let (ts, τ) ← instantiate σ; return (.op o ts τ, τ)
      | none => throw s!"operator {o}"
    | .unit => return (.unit, tUnitTy)
    | .tuple e1 e2 e3 => do
      let (a1, τ1) ← inferExp f C e1
      let (a2, τ2) ← inferExp f C e2
      match e3 with
      | none => return (.tuple a1 a2 none, tupleTy τ1 τ2 none)
      | some e => do
        let (a3, τ3) ← inferExp f C e
        return (.tuple a1 a2 (some a3), tupleTy τ1 τ2 (some τ3))
    | .nil => do let α ← freshTy .any; return (.nil (listTy α), listTy α)
    | .record row =>
      match row with
      | none => return (.record none, .record [] none)
      | some r => do
        let (ar, ρ) ← inferExpRow f C r
        return (.record (some ar), .record ρ none)
    | .update x row => do
      let (ts, τx) ← lookupInst C ⟨none, x⟩
      let (ar, ρ) ← inferExpRow f C row
      let e ← freshRow (ρ.map (·.1))
      unifyM τx (.record ρ (some e))
      return (.update x ts τx ar, τx)
    | .letE (.val vb) e => do
      let (avb, VEc) ← inferGroup f C vb
      let (ae, τ) ← inferExp f (C.plusVE VEc) e
      return (.letE (.val [] avb) ae, τ)
    | .paren e => do let (ae, τ) ← inferExp f C e; return (.paren ae, τ)
def inferExpRow : Nat → Ctx → BExpRow → Inf (AExpRow × Row)
  | 0, _, _ => throw "fuel"
  | f + 1, C, .field l e rest => do
    let (ae, τ) ← inferExp f C e
    match rest with
    | none => return (.field l ae none, Row.modify [(l, τ)] [])
    | some r => do
      let (ar, ρ) ← inferExpRow f C r
      return (.field l ae (some ar), Row.modify [(l, τ)] ρ)
def inferExp : Nat → Ctx → BExp → Inf (AExp × Ty)
  | 0, _, _ => throw "fuel"
  | f + 1, C, e =>
    match e with
    | .atexp a => do let (aa, τ) ← inferAtExp f C a; return (.atexp aa, τ)
    | .app e a => do
      let (ae, τe) ← inferExp f C e
      let (aa, τa) ← inferAtExp f C a
      let β ← freshTy .any
      unifyM τe (.fn τa β)
      return (.app ae aa, β)
    | .lam p e => do
      let ap ← inferAtPat f C p
      let (ae, τ) ← inferExp f (C.plusVE ap.ve) e
      return (.lam ap ae, .fn ap.ty τ)
    | .caseE e m => do
      let (ae, τ) ← inferExp f C e
      let β ← freshTy .any
      let am ← inferMatch f C τ β m
      return (.caseE ae am, β)
def inferMatch : Nat → Ctx → Ty → Ty → BMatch → Inf AMatch
  | 0, _, _, _, _ => throw "fuel"
  | f + 1, C, τ, β, .mk (.mk p e) rest => do
    let ap ← inferPat f C p
    unifyM ap.ty τ
    let (ae, τe) ← inferExp f (C.plusVE ap.ve) e
    unifyM τe β
    match rest with
    | none => return .mk (.mk ap ae) none
    | some m => do
      let am ← inferMatch f C τ β m
      return .mk (.mk ap ae) (some am)
/-- A group (r:s-dec-group, r:sm-topdec-value): the annotated binding, and the closed VE. -/
def inferGroup : Nat → Ctx → BValBind → Inf (AValBind × ValEnv)
  | 0, _, _ => throw "fuel"
  | f + 1, C, vb =>
    match vb with
    | .pat p e => do
      let ap ← inferAtPat f C p
      let (ae, τ) ← inferExp f (C.plusVE ap.ve) e
      unifyM τ ap.ty
      let s ← get
      return (.pat ap ae, closGroup (zonkCtx s C).tyvars (zonkVE s ap.ve))
    | .var .. => do
      let members := groupMembers vb
      let entries ← members.mapM fun (x, ann, e) => do
        match ann with
        | none => return (x, (none : Option (BTy × List BVar)), ← freshTy .any, e)
        | some ty =>
          let U' := annVars C.U ty
          match elabTy (C.plusU U') ty with
          | some τ => return (x, some (ty, U'), τ, e)
          | none => throw s!"the annotation of {x} does not elaborate"
      let VE : ValEnv := entries.foldr (fun m acc =>
        FMap.modify [(m.1, (if m.2.1.isSome then annScheme (annU m.2.1) m.2.2.1 else mono m.2.2.1, .v))] acc) []
      let C1 := C.plusVE VE
      let aes ← entries.mapM fun m => do
        let (ae, τe) ← inferExp f (C1.plusU (annU m.2.1)) m.2.2.2
        unifyM τe m.2.2.1
        let s ← get
        let A := (zonkCtx s C1).tyvars
        if (annU m.2.1).any (fun v => decide (v ∈ A)) then throw s!"an explicit variable of {m.1} escapes"
        return (m.1, m.2.1, m.2.2.1, ae)
      match buildVarBind aes with
      | some avb => do
        let s ← get
        return (avb, closGroup (zonkCtx s C).tyvars (zonkVE s VE))
      | none => throw "empty group"
end

/-! ## Applying the final substitution to an annotated phrase -/

section
variable (s : InfState)

def zt (τ : Ty) : Ty := zonk s fuel0 τ

mutual
def zAtPat : AAtPat → AAtPat
  | .wild τ => .wild (zt s τ)
  | .scon sc τ => .scon sc (zt s τ)
  | .var x τ => .var x (zt s τ)
  | .con lc inst τ => .con lc (inst.map (zt s)) (zt s τ)
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (zPat p1) (zPat p2) (zPatOpt p3)
  | .nil τ => .nil (zt s τ)
  | .record row τ => .record (zPatRowOpt row) (zt s τ)
  | .paren p => .paren (zPat p)
def zPatRow : APatRow → APatRow
  | .field l τ rest => .field l (zt s τ) (zPatRowOpt rest)
def zPatRowOpt : Option APatRow → Option APatRow
  | none => none
  | some r => some (zPatRow r)
def zPat : APat → APat
  | .atpat a => .atpat (zAtPat a)
  | .con lc inst args τ => .con lc (inst.map (zt s)) (zAtPats args) (zt s τ)
  | .cons p1 p2 => .cons (zPat p1) (zPat p2)
  | .as p x => .as (zPat p) x
def zPatOpt : Option APat → Option APat
  | none => none
  | some p => some (zPat p)
def zAtPats : List AAtPat → List AAtPat
  | [] => []
  | a :: as => zAtPat a :: zAtPats as
end

mutual
def zAtExp : AAtExp → AAtExp
  | .scon sc τ => .scon sc (zt s τ)
  | .var lv inst τ => .var lv (inst.map (zt s)) (zt s τ)
  | .con lc inst τ => .con lc (inst.map (zt s)) (zt s τ)
  | .op o inst τ => .op o (inst.map (zt s)) (zt s τ)
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (zExp e1) (zExp e2) (zExpOpt e3)
  | .nil τ => .nil (zt s τ)
  | .record row => .record (zExpRowOpt row)
  | .update x inst τ row => .update x (inst.map (zt s)) (zt s τ) (zExpRow row)
  | .letE (.val _ vb) e =>
    let vb' := zValBind vb
    .letE (.val vb'.ve vb') (zExp e)
  | .paren e => .paren (zExp e)
def zExpRow : AExpRow → AExpRow
  | .field l e rest => .field l (zExp e) (zExpRowOpt rest)
def zExpRowOpt : Option AExpRow → Option AExpRow
  | none => none
  | some r => some (zExpRow r)
def zExp : AExp → AExp
  | .atexp a => .atexp (zAtExp a)
  | .app e a => .app (zExp e) (zAtExp a)
  | .lam p e => .lam (zAtPat s p) (zExp e)
  | .caseE e m => .caseE (zExp e) (zMatch m)
def zExpOpt : Option AExp → Option AExp
  | none => none
  | some e => some (zExp e)
def zMatch : AMatch → AMatch
  | .mk (.mk p e) rest => .mk (.mk (zPat s p) (zExp e)) (zMatchOpt rest)
def zMatchOpt : Option AMatch → Option AMatch
  | none => none
  | some m => some (zMatch m)
def zValBind : AValBind → AValBind
  | .var x ann τ e rest => .var x ann (zt s τ) (zExp e) (zValBindOpt rest)
  | .pat p e => .pat (zAtPat s p) (zExp e)
def zValBindOpt : Option AValBind → Option AValBind
  | none => none
  | some vb => some (zValBind vb)
end
end

/-- Infer a closed expression phrase in C, from a fresh state, and apply the final substitution. -/
def runInf {α : Type} (m : Inf α) : Except String (α × InfState) := m.run {}

/-! ## Modules -/

/-- The fixed point of r:sm-topdec-types (B5): the custom types get the given names; the aliases
    are elaborated in Appendix A's order, each in C ⊕ (the custom types and the earlier aliases);
    then everything is recomputed in C ⊕ TE until TE is stable. -/
def elabTypesInf (C : Ctx) (db : Option BDatBind) (tbs : List BTypBind) (base : Nat) :
    Except String (TyEnv × ValEnv) := do
  let customs := db.getD []
  let TE0 : TyEnv := (customs.zipIdx).map fun (d, i) => (d.1, ((TyName.mk (base + i) d.2.1.length).toFcn, []))
  let TEa ← tbs.foldlM (fun (acc : TyEnv) tb =>
    match elabTypBind (C.oplusTE acc) tb with
    | some (_, TE) => pure (FMap.modify acc TE)
    | none => throw s!"the alias {tb.c} does not elaborate") TE0
  let step (TE : TyEnv) : Except String (TyEnv × ValEnv) :=
    let Cte := C.oplusTE TE
    match db with
    | none =>
      match elabTypBinds Cte tbs with
      | some (VEs, TEs) => pure (FMap.plusAll TEs, FMap.plusAll VEs)
      | none => throw "the aliases do not elaborate"
    | some d =>
      match elabDatBind Cte (namesOf TE) d, elabTypBinds Cte tbs with
      | some (VE', TE'), some (VEs, TEs) => pure (FMap.modify TE' (FMap.plusAll TEs), FMap.modify VE' (FMap.plusAll VEs))
      | none, _ => throw "the custom types do not elaborate"
      | _, none => throw "the aliases do not elaborate"
  let r1 ← step TEa
  let r2 ← step r1.1
  let r3 ← step r2.1
  if r3.1 == r2.1 then pure r3 else throw "type declarations: no fixed point"

def inferTopDec (C : Ctx) (base : Nat) : BTopDec → Except String (ATopDec × Env × PortEnv × Nat)
  | .value vb => do
    let ((avb, _), s) ← runInf (inferGroup fuel0 C vb)
    let avb' := zValBind s avb
    let a := ATopDec.value avb'.ve avb'
    match checkTopDec C a with
    | some (E, PE) => pure (a, E, PE, base)
    | none => throw s!"value group {repr ((groupMembers vb).map (·.1))}: the certificate does not check"
  | .types db tbs => do
    let (TE, VE) ← elabTypesInf C db tbs base
    let a := ATopDec.types TE VE db tbs
    match checkTopDec C a with
    | some (E, PE) => pure (a, E, PE, base + (db.getD []).length)
    | none => throw "type declarations: the certificate does not check"
  | .port x ty =>
    let U := annVars C.U ty
    let a := ATopDec.port x ty U
    match checkTopDec C a with
    | some (E, PE) => pure (a, E, PE, base)
    | none => throw s!"port {x} does not elaborate"
  | .seq d1 d2 => do
    let (a1, E1, PE1, b1) ← inferTopDec C base d1
    let (a2, E2, PE2, b2) ← inferTopDec (C.oplusE E1) b1 d2
    pure (.seq a1 a2, E1.plus E2, Env.plusPE PE1 PE2, b2)

/-- A module's annotated derivation, in the context C of its imports. -/
def inferModuleIn (B : SBasis) (C : Ctx) (m : BModule) : Except String AModule := do
  let body ← match m.body with
    | none => pure none
    | some d => do
      let (a, _, _, _) ← inferTopDec C (1000 + B.T.length) d
      pure (some a)
  pure ⟨m.header, m.imports, body⟩

def inferModule (B : SBasis) (m : BModule) : Except String AModule :=
  match importCtx B m.imports with
  | none => throw s!"module {m.header.name}: the imports do not elaborate"
  | some C => inferModuleIn B C m

theorem inferModule_of_ctx {B : SBasis} {m : BModule} {C : Ctx} (h : importCtx B m.imports = some C) :
    inferModule B m = inferModuleIn B C m := by
  simp only [inferModule, h]

/-- The modules of a program, each in the basis the earlier ones build. -/
def inferProgramFrom (B : SBasis) : List BModule → Except String AProgram
  | [] => pure []
  | m :: ms => do
    let a ← inferModule B m
    match a.result B with
    | some (B', _) => do
      let rest ← inferProgramFrom (B.plus B') ms
      pure (a :: rest)
    | none => throw s!"module {m.header.name}: the certificate does not check"

def inferProgram (B : SBasis) (p : BProgram) : Except String AProgram := inferProgramFrom B p.modules

end StandardElm.Stat
