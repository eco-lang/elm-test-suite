/-
  A Standard Definition of Elm? Mechanisation: renamings of annotated phrases, plan step 10 (Lean
  definitions, "Renamings": `AnnModule.rename`, `AnnProgram.rename`).

  A renaming (Rename.lean) is applied to every semantic object an annotated phrase records: the
  types at its leaves and binders, the instances at its occurrences, the value environments of its
  declarations, the U' of its annotations, the type and value environments of its type
  declarations and the U of its ports. The bare syntax it carries (identifiers, type expressions,
  type declarations) is unchanged, so a renamed phrase erases to the same bare phrase
  (`erase_rename`).
-/
import StandardElmMech.Stat.Rename

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Environments -/

def Renaming.valEnv (r : Renaming) (VE : ValEnv) : ValEnv :=
  VE.map fun p => (p.1, (r.scheme p.2.1, p.2.2))

def Renaming.tyFcn (r : Renaming) (θ : TyFcn) : TyFcn := ⟨θ.params.map r.bvar, r.ty θ.body⟩

def Renaming.tyEnv (r : Renaming) (TE : TyEnv) : TyEnv :=
  TE.map fun p => (p.1, (r.tyFcn p.2.1, r.valEnv p.2.2))

def Renaming.iEnv (r : Renaming) (I : IEnv) : IEnv := ⟨r.tyEnv I.TE, r.valEnv I.VE⟩

def Renaming.env (r : Renaming) (E : Env) : Env :=
  ⟨E.QE.map (fun p => (p.1, r.iEnv p.2)), r.tyEnv E.TE, r.valEnv E.VE⟩

def Renaming.ctx (r : Renaming) (C : Ctx) : Ctx := ⟨C.T.map r.tnApply, C.U.map r.bvar, r.env C.E⟩

def Renaming.ann (r : Renaming) : Option (Src.BTy × List BVar) → Option (Src.BTy × List BVar)
  | none => none
  | some (ty, U) => some (ty, U.map r.bvar)

/-! ## Patterns -/

mutual
def Renaming.atPat (r : Renaming) : AAtPat → AAtPat
  | .wild τ => .wild (r.ty τ)
  | .scon sc τ => .scon sc (r.ty τ)
  | .var x τ => .var x (r.ty τ)
  | .con lc inst τ => .con lc (r.tys inst) (r.ty τ)
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (r.pat p1) (r.pat p2) (r.patOpt p3)
  | .nil τ => .nil (r.ty τ)
  | .record row τ => .record (r.patRowOpt row) (r.ty τ)
  | .paren p => .paren (r.pat p)
def Renaming.patRow (r : Renaming) : APatRow → APatRow
  | .field l τ rest => .field l (r.ty τ) (r.patRowOpt rest)
def Renaming.patRowOpt (r : Renaming) : Option APatRow → Option APatRow
  | none => none
  | some row => some (r.patRow row)
def Renaming.pat (r : Renaming) : APat → APat
  | .atpat a => .atpat (r.atPat a)
  | .con lc inst args τ => .con lc (r.tys inst) (r.atPats args) (r.ty τ)
  | .cons p1 p2 => .cons (r.pat p1) (r.pat p2)
  | .as p x => .as (r.pat p) x
def Renaming.patOpt (r : Renaming) : Option APat → Option APat
  | none => none
  | some p => some (r.pat p)
def Renaming.atPats (r : Renaming) : List AAtPat → List AAtPat
  | [] => []
  | a :: as => r.atPat a :: r.atPats as
end

/-! ## Expressions -/

mutual
def Renaming.atExp (r : Renaming) : AAtExp → AAtExp
  | .scon sc τ => .scon sc (r.ty τ)
  | .var lv inst τ => .var lv (r.tys inst) (r.ty τ)
  | .con lc inst τ => .con lc (r.tys inst) (r.ty τ)
  | .op o inst τ => .op o (r.tys inst) (r.ty τ)
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (r.exp e1) (r.exp e2) (r.expOpt e3)
  | .nil τ => .nil (r.ty τ)
  | .record row => .record (r.expRowOpt row)
  | .update x inst τ row => .update x (r.tys inst) (r.ty τ) (r.expRow row)
  | .letE d e => .letE (r.dec d) (r.exp e)
  | .paren e => .paren (r.exp e)
def Renaming.expRow (r : Renaming) : AExpRow → AExpRow
  | .field l e rest => .field l (r.exp e) (r.expRowOpt rest)
def Renaming.expRowOpt (r : Renaming) : Option AExpRow → Option AExpRow
  | none => none
  | some row => some (r.expRow row)
def Renaming.exp (r : Renaming) : AExp → AExp
  | .atexp a => .atexp (r.atExp a)
  | .app e a => .app (r.exp e) (r.atExp a)
  | .lam p e => .lam (r.atPat p) (r.exp e)
  | .caseE e m => .caseE (r.exp e) (r.match_ m)
def Renaming.expOpt (r : Renaming) : Option AExp → Option AExp
  | none => none
  | some e => some (r.exp e)
def Renaming.match_ (r : Renaming) : AMatch → AMatch
  | .mk mr rest => .mk (r.mrule mr) (r.matchOpt rest)
def Renaming.matchOpt (r : Renaming) : Option AMatch → Option AMatch
  | none => none
  | some m => some (r.match_ m)
def Renaming.mrule (r : Renaming) : AMRule → AMRule
  | .mk p e => .mk (r.pat p) (r.exp e)
def Renaming.dec (r : Renaming) : ADec → ADec
  | .val VE vb => .val (r.valEnv VE) (r.valBind vb)
def Renaming.valBind (r : Renaming) : AValBind → AValBind
  | .var x ann τ e rest => .var x (r.ann ann) (r.ty τ) (r.exp e) (r.valBindOpt rest)
  | .pat p e => .pat (r.atPat p) (r.exp e)
def Renaming.valBindOpt (r : Renaming) : Option AValBind → Option AValBind
  | none => none
  | some vb => some (r.valBind vb)
end

/-! ## Modules and programs -/

def Renaming.topDec (r : Renaming) : ATopDec → ATopDec
  | .value VE vb => .value (r.valEnv VE) (r.valBind vb)
  | .types TE VE db tbs => .types (r.tyEnv TE) (r.valEnv VE) db tbs
  | .port x ty U => .port x ty (U.map r.bvar)
  | .seq a1 a2 => .seq (r.topDec a1) (r.topDec a2)

def AModule.rename (r : Renaming) (a : AModule) : AModule := ⟨a.header, a.imports, a.body.map r.topDec⟩

def AProgram.rename (r : Renaming) (a : AProgram) : AProgram := a.map (·.rename r)

/-! ## A renamed phrase erases to the same bare phrase -/

mutual
theorem erase_atPat (r : Renaming) : (p : AAtPat) → (r.atPat p).erase = p.erase
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .unit | .nil _ => rfl
  | .tuple p1 p2 p3 => by
    simp only [Renaming.atPat, AAtPat.erase, erase_pat r p1, erase_pat r p2, erase_patOpt r p3]
  | .record row _ => by simp only [Renaming.atPat, AAtPat.erase, erase_patRowOpt r row]
  | .paren p => by simp only [Renaming.atPat, AAtPat.erase, erase_pat r p]
theorem erase_patRow (r : Renaming) : (row : APatRow) → (r.patRow row).erase = row.erase
  | .field l _ rest => by simp only [Renaming.patRow, APatRow.erase, erase_patRowOpt r rest]
theorem erase_patRowOpt (r : Renaming) : (row : Option APatRow) →
    APatRow.eraseOpt (r.patRowOpt row) = APatRow.eraseOpt row
  | none => rfl
  | some row => by simp only [Renaming.patRowOpt, APatRow.eraseOpt, erase_patRow r row]
theorem erase_pat (r : Renaming) : (p : APat) → (r.pat p).erase = p.erase
  | .atpat a => by simp only [Renaming.pat, APat.erase, erase_atPat r a]
  | .con lc _ args _ => by simp only [Renaming.pat, APat.erase, erase_atPats r args]
  | .cons p1 p2 => by simp only [Renaming.pat, APat.erase, erase_pat r p1, erase_pat r p2]
  | .as p x => by simp only [Renaming.pat, APat.erase, erase_pat r p]
theorem erase_patOpt (r : Renaming) : (p : Option APat) → APat.eraseOpt (r.patOpt p) = APat.eraseOpt p
  | none => rfl
  | some p => by simp only [Renaming.patOpt, APat.eraseOpt, erase_pat r p]
theorem erase_atPats (r : Renaming) : (ps : List AAtPat) → AAtPat.eraseList (r.atPats ps) = AAtPat.eraseList ps
  | [] => rfl
  | p :: ps => by simp only [Renaming.atPats, AAtPat.eraseList, erase_atPat r p, erase_atPats r ps]
end

mutual
theorem erase_atExp (r : Renaming) : (a : AAtExp) → (r.atExp a).erase = a.erase
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .unit | .nil _ => rfl
  | .tuple e1 e2 e3 => by
    simp only [Renaming.atExp, AAtExp.erase, erase_exp r e1, erase_exp r e2, erase_expOpt r e3]
  | .record row => by simp only [Renaming.atExp, AAtExp.erase, erase_expRowOpt r row]
  | .update x _ _ row => by simp only [Renaming.atExp, AAtExp.erase, erase_expRow r row]
  | .letE d e => by simp only [Renaming.atExp, AAtExp.erase, erase_dec r d, erase_exp r e]
  | .paren e => by simp only [Renaming.atExp, AAtExp.erase, erase_exp r e]
theorem erase_expRow (r : Renaming) : (row : AExpRow) → (r.expRow row).erase = row.erase
  | .field l e rest => by simp only [Renaming.expRow, AExpRow.erase, erase_exp r e, erase_expRowOpt r rest]
theorem erase_expRowOpt (r : Renaming) : (row : Option AExpRow) →
    AExpRow.eraseOpt (r.expRowOpt row) = AExpRow.eraseOpt row
  | none => rfl
  | some row => by simp only [Renaming.expRowOpt, AExpRow.eraseOpt, erase_expRow r row]
theorem erase_exp (r : Renaming) : (e : AExp) → (r.exp e).erase = e.erase
  | .atexp a => by simp only [Renaming.exp, AExp.erase, erase_atExp r a]
  | .app e a => by simp only [Renaming.exp, AExp.erase, erase_exp r e, erase_atExp r a]
  | .lam p e => by simp only [Renaming.exp, AExp.erase, erase_atPat r p, erase_exp r e]
  | .caseE e m => by simp only [Renaming.exp, AExp.erase, erase_exp r e, erase_match r m]
theorem erase_expOpt (r : Renaming) : (e : Option AExp) → AExp.eraseOpt (r.expOpt e) = AExp.eraseOpt e
  | none => rfl
  | some e => by simp only [Renaming.expOpt, AExp.eraseOpt, erase_exp r e]
theorem erase_match (r : Renaming) : (m : AMatch) → (r.match_ m).erase = m.erase
  | .mk mr rest => by simp only [Renaming.match_, AMatch.erase, erase_mrule r mr, erase_matchOpt r rest]
theorem erase_matchOpt (r : Renaming) : (m : Option AMatch) → AMatch.eraseOpt (r.matchOpt m) = AMatch.eraseOpt m
  | none => rfl
  | some m => by simp only [Renaming.matchOpt, AMatch.eraseOpt, erase_match r m]
theorem erase_mrule (r : Renaming) : (mr : AMRule) → (r.mrule mr).erase = mr.erase
  | .mk p e => by simp only [Renaming.mrule, AMRule.erase, erase_pat r p, erase_exp r e]
theorem erase_dec (r : Renaming) : (d : ADec) → (r.dec d).erase = d.erase
  | .val _ vb => by simp only [Renaming.dec, ADec.erase, erase_valBind r vb]
theorem erase_valBind (r : Renaming) : (vb : AValBind) → (r.valBind vb).erase = vb.erase
  | .var x ann _ e rest => by
    have ha : (r.ann ann).map Prod.fst = ann.map Prod.fst := by
      cases ann with
      | none => rfl
      | some p => rfl
    simp only [Renaming.valBind, AValBind.erase, ha, erase_exp r e, erase_valBindOpt r rest]
  | .pat p e => by simp only [Renaming.valBind, AValBind.erase, erase_atPat r p, erase_exp r e]
theorem erase_valBindOpt (r : Renaming) : (vb : Option AValBind) →
    AValBind.eraseOpt (r.valBindOpt vb) = AValBind.eraseOpt vb
  | none => rfl
  | some vb => by simp only [Renaming.valBindOpt, AValBind.eraseOpt, erase_valBind r vb]
end

theorem erase_topDec (r : Renaming) : (d : ATopDec) → (r.topDec d).erase = d.erase
  | .value _ vb => by simp only [Renaming.topDec, ATopDec.erase, erase_valBind r vb]
  | .types _ _ _ _ => rfl
  | .port _ _ _ => rfl
  | .seq a1 a2 => by simp only [Renaming.topDec, ATopDec.erase, erase_topDec r a1, erase_topDec r a2]

theorem AModule.erase_rename (r : Renaming) (a : AModule) : (a.rename r).erase = a.erase := by
  rcases a with ⟨h, imps, body⟩
  cases body with
  | none => rfl
  | some d => simp only [AModule.rename, AModule.erase, Option.map_some, erase_topDec r d]

theorem AProgram.erase_rename (r : Renaming) (a : AProgram) :
    (a.rename r).map AModule.erase = a.map AModule.erase := by
  simp only [AProgram.rename, List.map_map]
  congr 1
  funext m
  exact AModule.erase_rename r m

end StandardElm.Stat
