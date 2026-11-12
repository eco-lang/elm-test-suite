/-
  A Standard Definition of Elm? Mechanisation: the checker of annotated Core phrases commutes with
  a renaming of type names (plan step 10, transport across bases, second layer): the types,
  value environments and rows computed from a phrase, the closure of a declaration, the checker
  itself and the nodes of the derivation.
-/
import StandardElmMech.Stat.NameRen

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

section
variable {ρ : List (TyName × TyName)}

/-! ## Fixed types -/

mutual
theorem nr_ty_fixed (h : NR ρ) : (τ : Ty) → (∀ t ∈ τ.tynames, t ∈ T0) → (nr ρ).ty τ = τ
  | .var _, _ => rfl
  | .record r tl, hn => by simp only [nr_ty_record]; rw [nr_row_fixed h r hn]
  | .fn a b, hn => by
    simp only [Ty.tynames, List.mem_append] at hn
    simp only [nr_ty_fn]
    rw [nr_ty_fixed h a (fun t ht => hn t (.inl ht)), nr_ty_fixed h b (fun t ht => hn t (.inr ht))]
  | .con as t, hn => by
    simp only [Ty.tynames, List.mem_cons] at hn
    simp only [nr_ty_con]
    rw [← nr_tys, nr_list_fixed h as (fun u hu => hn u (.inr hu)), (h.fix (hn t (.inl rfl)))]
theorem nr_row_fixed (h : NR ρ) : (r : Row) → (∀ t ∈ Ty.rowTynames r, t ∈ T0) → (nr ρ).row r = r
  | [], _ => rfl
  | (l, τ) :: rest, hn => by
    simp only [Ty.rowTynames, List.mem_append] at hn
    simp only [nr_row_cons]
    rw [nr_ty_fixed h τ (fun t ht => hn t (.inl ht)), nr_row_fixed h rest (fun t ht => hn t (.inr ht))]
theorem nr_list_fixed (h : NR ρ) : (l : List Ty) → (∀ t ∈ Ty.listTynames l, t ∈ T0) → (nr ρ).tys l = l
  | [], _ => rfl
  | τ :: rest, hn => by
    simp only [Ty.listTynames, List.mem_append] at hn
    simp only [Renaming.tys]
    rw [nr_ty_fixed h τ (fun t ht => hn t (.inl ht)), nr_list_fixed h rest (fun t ht => hn t (.inr ht))]
end

theorem OTstat_names : ∀ p ∈ OTstatList, ∀ t ∈ p.2.1.body.tynames, t ∈ T0 := by decide

theorem nr_OTstat (h : NR ρ) {o : Op} {σ : Scheme} {st : IdStatus} (ho : OTstat o = some (σ, st)) :
    (nr ρ).scheme σ = σ := by
  have hm := find?_mem ho
  have := OTstat_names _ hm
  show (⟨σ.bound.map (nr ρ).bvar, (nr ρ).ty σ.body⟩ : Scheme) = σ
  rw [nr_bvar_fun, List.map_id', nr_ty_fixed h σ.body this]

theorem nr_typeOf (h : NR ρ) (sc : Src.SLit) : (nr ρ).scheme (typeOf sc) = typeOf sc := by
  cases sc <;> simp [typeOf, Renaming.scheme, mono, nr_tFloatTy h, nr_tCharTy h, nr_tStringTy h]

theorem nr_litInst (sc : Src.SLit) (τ : Ty) : litInst sc ((nr ρ).ty τ) = (litInst sc τ).map (nr ρ).ty := by
  cases sc <;> rfl

theorem nr_mem_fixed (h : NR ρ) (τ : Ty) (l : List Ty) (hl : ∀ x ∈ l, (nr ρ).ty x = x) :
    decide ((nr ρ).ty τ ∈ l) = decide (τ ∈ l) := by
  apply decide_eq_decide.mpr
  constructor
  · intro hm
    have : (nr ρ).ty τ = (nr ρ).ty ((nr ρ).ty τ) := (hl _ hm).symm
    rw [nr_ty_inj h _ _ this]; exact hm
  · intro hm; rw [hl τ hm]; exact hm

theorem nr_ty_eq_iff (h : NR ρ) (τ τ' : Ty) : (nr ρ).ty τ = (nr ρ).ty τ' ↔ τ = τ' :=
  ⟨nr_ty_inj h τ τ', fun e => e ▸ rfl⟩

theorem nr_isConTy (τ : Ty) : isConTy ((nr ρ).ty τ) = isConTy τ := by cases τ <;> rfl
theorem nr_isRecordTy (τ : Ty) : isRecordTy ((nr ρ).ty τ) = isRecordTy τ := by cases τ <;> simp [isRecordTy]
theorem nr_recordRow (τ : Ty) : recordRow ((nr ρ).ty τ) = (nr ρ).row (recordRow τ) := by
  cases τ <;> simp [recordRow]
theorem nr_isListTy (h : NR ρ) (τ : Ty) : isListTy ((nr ρ).ty τ) = isListTy τ := by
  rcases τ with _ | _ | _ | ⟨_ | ⟨τ1, _ | ⟨τ2, rest⟩⟩, t⟩ <;> simp [isListTy]
  exact h.beq (by decide) t
theorem nr_cod (τ : Ty) : ((nr ρ).ty τ).cod = (nr ρ).ty τ.cod := by cases τ <;> rfl
theorem nr_arrows (l : List Ty) (τ : Ty) : arrows (l.map (nr ρ).ty) ((nr ρ).ty τ) = (nr ρ).ty (arrows l τ) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [arrows, ih]

theorem nr_scheme_inj (h : NR ρ) (σ σ' : Scheme) (e : (nr ρ).scheme σ = (nr ρ).scheme σ') : σ = σ' := by
  rcases σ with ⟨b, t⟩; rcases σ' with ⟨b', t'⟩
  simp only [Renaming.scheme, nr_bvar_fun, List.map_id', Scheme.mk.injEq] at e
  rw [e.1, nr_ty_inj h _ _ e.2]

theorem nr_valEnv_inj (h : NR ρ) : (VE VE' : ValEnv) → (nr ρ).valEnv VE = (nr ρ).valEnv VE' → VE = VE'
  | [], [], _ => rfl
  | (x, σ, st) :: r, (x', σ', st') :: r', e => by
    simp only [Renaming.valEnv, List.map_cons, List.cons.injEq, Prod.mk.injEq] at e
    rw [e.1.1, nr_scheme_inj h _ _ e.1.2.1, e.1.2.2, nr_valEnv_inj h r r' e.2]
  | [], (_, _, _) :: _, e | (_, _, _) :: _, [], e => by simp [Renaming.valEnv] at e

/-! ## Types, environments and rows computed from a phrase -/

mutual
theorem nr_atPat_ty (h : NR ρ) : (p : AAtPat) → ((nr ρ).atPat p).ty = (nr ρ).ty p.ty
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .record _ _ => rfl
  | .unit => (nr_tUnitTy h).symm
  | .tuple p1 p2 p3 => by
    simp only [Renaming.atPat, AAtPat.ty, nr_pat_ty h p1, nr_pat_ty h p2, nr_patOpt_ty h p3, nr_tupleTy h]
  | .paren p => by simp only [Renaming.atPat, AAtPat.ty]; exact nr_pat_ty h p
theorem nr_pat_ty (h : NR ρ) : (p : APat) → ((nr ρ).pat p).ty = (nr ρ).ty p.ty
  | .atpat a => by simp only [Renaming.pat, APat.ty]; exact nr_atPat_ty h a
  | .con _ _ _ _ => rfl
  | .cons p1 _ => by simp only [Renaming.pat, APat.ty, nr_pat_ty h p1, nr_listTy h]
  | .as p _ => by simp only [Renaming.pat, APat.ty]; exact nr_pat_ty h p
theorem nr_patOpt_ty (h : NR ρ) : (p : Option APat) → APat.tyOpt ((nr ρ).patOpt p) = (APat.tyOpt p).map (nr ρ).ty
  | none => rfl
  | some p => by simp only [Renaming.patOpt, APat.tyOpt, nr_pat_ty h p, Option.map_some]
end

theorem nr_atPats_tyList (h : NR ρ) : (ps : List AAtPat) → AAtPat.tyList ((nr ρ).atPats ps) = (AAtPat.tyList ps).map (nr ρ).ty
  | [] => rfl
  | p :: ps => by simp [Renaming.atPats, AAtPat.tyList, nr_atPat_ty h p, nr_atPats_tyList h ps]

mutual
theorem nr_atPat_ve (h : NR ρ) : (p : AAtPat) → ((nr ρ).atPat p).ve = (nr ρ).valEnv p.ve
  | .wild _ | .scon _ _ | .con _ _ _ | .unit | .nil _ => rfl
  | .var _ _ => rfl
  | .tuple p1 p2 p3 => by
    simp only [Renaming.atPat, AAtPat.ve, nr_pat_ve h p1, nr_pat_ve h p2, nr_patOpt_ve h p3, nr_valEnv_modify]
  | .record row _ => by simp only [Renaming.atPat, AAtPat.ve]; exact nr_patRowOpt_ve h row
  | .paren p => by simp only [Renaming.atPat, AAtPat.ve]; exact nr_pat_ve h p
theorem nr_patRow_ve (h : NR ρ) : (r : APatRow) → ((nr ρ).patRow r).ve = (nr ρ).valEnv r.ve
  | .field l τ rest => by
    simp only [Renaming.patRow, APatRow.ve, nr_patRowOpt_ve h rest, ← nr_valEnv_modify]; rfl
theorem nr_patRowOpt_ve (h : NR ρ) : (r : Option APatRow) → APatRow.veOpt ((nr ρ).patRowOpt r) = (nr ρ).valEnv (APatRow.veOpt r)
  | none => rfl
  | some r => by simp only [Renaming.patRowOpt, APatRow.veOpt]; exact nr_patRow_ve h r
theorem nr_pat_ve (h : NR ρ) : (p : APat) → ((nr ρ).pat p).ve = (nr ρ).valEnv p.ve
  | .atpat a => by simp only [Renaming.pat, APat.ve]; exact nr_atPat_ve h a
  | .con _ _ args _ => by
    simp only [Renaming.pat, APat.ve, nr_atPats_veList h args, nr_valEnv_plusAll]
  | .cons p1 p2 => by simp only [Renaming.pat, APat.ve, nr_pat_ve h p1, nr_pat_ve h p2, nr_valEnv_modify]
  | .as p x => by
    simp only [Renaming.pat, APat.ve, nr_pat_ve h p, nr_pat_ty h p, ← nr_valEnv_modify]; rfl
theorem nr_patOpt_ve (h : NR ρ) : (p : Option APat) → APat.veOpt ((nr ρ).patOpt p) = (nr ρ).valEnv (APat.veOpt p)
  | none => rfl
  | some p => by simp only [Renaming.patOpt, APat.veOpt]; exact nr_pat_ve h p
theorem nr_atPats_veList (h : NR ρ) : (ps : List AAtPat) → AAtPat.veList ((nr ρ).atPats ps) = (AAtPat.veList ps).map (nr ρ).valEnv
  | [] => rfl
  | p :: ps => by simp [Renaming.atPats, AAtPat.veList, nr_atPat_ve h p, nr_atPats_veList h ps]
end

mutual
theorem nr_patRow_row : (r : APatRow) → ((nr ρ).patRow r).row = (nr ρ).row r.row
  | .field l τ rest => by
    simp only [Renaming.patRow, APatRow.row, nr_patRowOpt_row rest, ← nr_rowModify]; rfl
theorem nr_patRowOpt_row : (r : Option APatRow) → APatRow.rowOpt ((nr ρ).patRowOpt r) = (nr ρ).row (APatRow.rowOpt r)
  | none => rfl
  | some r => by simp only [Renaming.patRowOpt, APatRow.rowOpt]; exact nr_patRow_row r
end

mutual
theorem nr_atExp_ty (h : NR ρ) : (a : AAtExp) → ((nr ρ).atExp a).ty = (nr ρ).ty a.ty
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .update _ _ _ _ => rfl
  | .unit => (nr_tUnitTy h).symm
  | .tuple e1 e2 e3 => by
    simp only [Renaming.atExp, AAtExp.ty, nr_exp_ty h e1, nr_exp_ty h e2, nr_expOpt_ty h e3, nr_tupleTy h]
  | .record row => by simp only [Renaming.atExp, AAtExp.ty, nr_expRowOpt_row h row, nr_ty_record]
  | .letE _ e => by simp only [Renaming.atExp, AAtExp.ty]; exact nr_exp_ty h e
  | .paren e => by simp only [Renaming.atExp, AAtExp.ty]; exact nr_exp_ty h e
theorem nr_expRow_row (h : NR ρ) : (r : AExpRow) → ((nr ρ).expRow r).row = (nr ρ).row r.row
  | .field l e rest => by
    simp only [Renaming.expRow, AExpRow.row, nr_expRowOpt_row h rest, nr_exp_ty h e, ← nr_rowModify]; rfl
theorem nr_expRowOpt_row (h : NR ρ) : (r : Option AExpRow) → AExpRow.rowOpt ((nr ρ).expRowOpt r) = (nr ρ).row (AExpRow.rowOpt r)
  | none => rfl
  | some r => by simp only [Renaming.expRowOpt, AExpRow.rowOpt]; exact nr_expRow_row h r
theorem nr_exp_ty (h : NR ρ) : (e : AExp) → ((nr ρ).exp e).ty = (nr ρ).ty e.ty
  | .atexp a => by simp only [Renaming.exp, AExp.ty]; exact nr_atExp_ty h a
  | .app e _ => by simp only [Renaming.exp, AExp.ty, nr_exp_ty h e, nr_cod]
  | .lam p e => by simp only [Renaming.exp, AExp.ty, nr_exp_ty h e, nr_atPat_ty h p, nr_ty_fn]
  | .caseE _ m => by simp only [Renaming.exp, AExp.ty, nr_match_ty h m, nr_cod]
theorem nr_expOpt_ty (h : NR ρ) : (e : Option AExp) → AExp.tyOpt ((nr ρ).expOpt e) = (AExp.tyOpt e).map (nr ρ).ty
  | none => rfl
  | some e => by simp only [Renaming.expOpt, AExp.tyOpt, nr_exp_ty h e, Option.map_some]
theorem nr_match_ty (h : NR ρ) : (m : AMatch) → ((nr ρ).match_ m).ty = (nr ρ).ty m.ty
  | .mk mr _ => by simp only [Renaming.match_, AMatch.ty]; exact nr_mrule_ty h mr
theorem nr_mrule_ty (h : NR ρ) : (mr : AMRule) → ((nr ρ).mrule mr).ty = (nr ρ).ty mr.ty
  | .mk p e => by simp only [Renaming.mrule, AMRule.ty, nr_exp_ty h e, nr_pat_ty h p, nr_ty_fn]
end

theorem nr_ann_annU (ann : Option (Src.BTy × List BVar)) : annU ((nr ρ).ann ann) = annU ann := by
  rcases ann with _ | ⟨t, U⟩ <;> simp [Renaming.ann, annU]

theorem nr_ann_isSome (ann : Option (Src.BTy × List BVar)) : ((nr ρ).ann ann).isSome = ann.isSome := by
  rcases ann with _ | ⟨t, U⟩ <;> rfl

theorem nr_ann_eq (ann : Option (Src.BTy × List BVar)) : (nr ρ).ann ann = ann := by
  rcases ann with _ | ⟨t, U⟩ <;> simp [Renaming.ann]

theorem nr_valBind_ve (h : NR ρ) : (vb : AValBind) → ((nr ρ).valBind vb).ve = (nr ρ).valEnv vb.ve
  | .var x ann τ e rest => by
    simp only [Renaming.valBind]
    rw [AValBind.ve_var, AValBind.ve_var, nr_ann_annU, nr_ann_isSome, ← nr_valEnv_modify]
    congr 1
    · split <;> simp [Renaming.valEnv, nr_annScheme h, nr_mono]
    · cases rest with
      | none => rfl
      | some vb => simp only [Renaming.valBindOpt]; exact nr_valBind_ve h vb
  | .pat p e => by simp only [Renaming.valBind, AValBind.ve]; exact nr_atPat_ve h p

theorem nr_dec_result (h : NR ρ) (C : Ctx) (d : ADec) :
    ((nr ρ).dec d).result ((nr ρ).ctx C) = (nr ρ).valEnv (d.result C) := by
  cases d with
  | val VE vb => simp only [Renaming.dec, ADec.result, nr_ctx_tyvars h, nr_closGroup h]

theorem nr_valEnv_dec (h : NR ρ) (VE VE' : ValEnv) :
    decide ((nr ρ).valEnv VE = (nr ρ).valEnv VE') = decide (VE = VE') :=
  decide_eq_decide.mpr ⟨nr_valEnv_inj h _ _, fun e => e ▸ rfl⟩

/-! ## The checker -/

theorem nr_lookupVal_c (C : Ctx) (lv : LongId) :
    (match ((nr ρ).ctx C).lookupVal lv with
     | some (σ, .c) => some σ
     | _ => none) = (match C.lookupVal lv with
     | some (σ, .c) => some ((nr ρ).scheme σ)
     | _ => none) := by
  rw [nr_lookupVal]
  rcases C.lookupVal lv with _ | ⟨σ, _ | _⟩ <;> rfl

mutual
theorem nr_checkAtPat (h : NR ρ) (C : Ctx) : (p : AAtPat) → checkAtPat ((nr ρ).ctx C) ((nr ρ).atPat p) = checkAtPat C p
  | .wild _ | .var _ _ | .unit => rfl
  | .scon sc τ => by
    simp only [Renaming.atPat, checkAtPat]
    rw [← nr_typeOf h sc, nr_litInst, nr_genAt h, nr_typeOf h sc,
      nr_mem_fixed h τ _ (by simp [nr_tIntTy h, nr_tCharTy h, nr_tStringTy h])]
  | .con lc inst τ => by
    simp only [Renaming.atPat, checkAtPat, nr_lookupVal]
    rcases C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_genAt h, nr_isConTy]
    · rfl
  | .tuple p1 p2 p3 => by
    simp only [Renaming.atPat, checkAtPat, nr_checkPat h C p1, nr_checkPat h C p2, nr_checkPatOpt h C p3]
  | .nil τ => by simp only [Renaming.atPat, checkAtPat]; exact nr_isListTy h τ
  | .record row τ => by
    simp only [Renaming.atPat, checkAtPat, nr_checkPatRowOpt h C row, nr_isRecordTy, nr_patRowOpt_row,
      nr_recordRow, nr_subB h]
  | .paren p => by simp only [Renaming.atPat, checkAtPat]; exact nr_checkPat h C p
theorem nr_checkPatRow (h : NR ρ) (C : Ctx) : (r : APatRow) → checkPatRow ((nr ρ).ctx C) ((nr ρ).patRow r) = checkPatRow C r
  | .field _ _ rest => by simp only [Renaming.patRow, checkPatRow]; exact nr_checkPatRowOpt h C rest
theorem nr_checkPatRowOpt (h : NR ρ) (C : Ctx) : (r : Option APatRow) →
    checkPatRowOpt ((nr ρ).ctx C) ((nr ρ).patRowOpt r) = checkPatRowOpt C r
  | none => rfl
  | some r => by simp only [Renaming.patRowOpt, checkPatRowOpt]; exact nr_checkPatRow h C r
theorem nr_checkPat (h : NR ρ) (C : Ctx) : (p : APat) → checkPat ((nr ρ).ctx C) ((nr ρ).pat p) = checkPat C p
  | .atpat a => by simp only [Renaming.pat, checkPat]; exact nr_checkAtPat h C a
  | .con lc inst args τ => by
    simp only [Renaming.pat, checkPat, nr_lookupVal, nr_checkAtPatList h C args]
    rcases C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_atPats_tyList h, nr_arrows, nr_genAt h, nr_isConTy]
    · rfl
  | .cons p1 p2 => by
    simp only [Renaming.pat, checkPat, nr_checkPat h C p1, nr_checkPat h C p2, nr_pat_ty h, ← nr_listTy h,
      nr_dec_ty h]
  | .as p _ => by simp only [Renaming.pat, checkPat]; exact nr_checkPat h C p
theorem nr_checkPatOpt (h : NR ρ) (C : Ctx) : (p : Option APat) → checkPatOpt ((nr ρ).ctx C) ((nr ρ).patOpt p) = checkPatOpt C p
  | none => rfl
  | some p => by simp only [Renaming.patOpt, checkPatOpt]; exact nr_checkPat h C p
theorem nr_checkAtPatList (h : NR ρ) (C : Ctx) : (ps : List AAtPat) →
    checkAtPatList ((nr ρ).ctx C) ((nr ρ).atPats ps) = checkAtPatList C ps
  | [] => rfl
  | p :: ps => by simp only [Renaming.atPats, checkAtPatList, nr_checkAtPat h C p, nr_checkAtPatList h C ps]
end

theorem nr_checkAnn (h : NR ρ) (C : Ctx) (ann : Option (Src.BTy × List BVar)) (τ : Ty) :
    checkAnn ((nr ρ).ctx C) ((nr ρ).ann ann) ((nr ρ).ty τ) = checkAnn C ann τ := by
  rcases ann with _ | ⟨t, U⟩
  · rfl
  · simp only [Renaming.ann, nr_bvar_fun, List.map_id', checkAnn, nr_ctx_U, nr_plusU, nr_elabTy h, nr_ctx_tyvars h]
    congr 2
    cases elabTy (C.plusU U) t with
    | none => simp
    | some τ' =>
      simp only [Option.map_some, Option.some.injEq]
      exact decide_eq_decide.mpr ⟨nr_ty_inj h _ _, fun e => e ▸ rfl⟩

theorem nr_fnMatch (h : NR ρ) (τ τ0 : Ty) :
    (match (nr ρ).ty τ with
     | .fn τ' _ => decide (τ' = (nr ρ).ty τ0)
     | _ => false) = (match τ with
     | .fn τ' _ => decide (τ' = τ0)
     | _ => false) := by
  cases τ with
  | fn a b => simp only [nr_ty_fn]; exact nr_dec_ty h a τ0
  | var _ => rfl
  | record _ _ => simp
  | con _ _ => simp

mutual
theorem nr_checkAtExp (h : NR ρ) (C : Ctx) : (a : AAtExp) → checkAtExp ((nr ρ).ctx C) ((nr ρ).atExp a) = checkAtExp C a
  | .scon sc τ => by
    simp only [Renaming.atExp, checkAtExp]
    rw [← nr_typeOf h sc, nr_litInst, nr_genAt h, nr_typeOf h sc]
  | .var lv inst τ => by
    simp only [Renaming.atExp, checkAtExp, nr_lookupVal]
    rcases C.lookupVal lv with _ | ⟨σ, st⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_genAt h]
  | .con lc inst τ => by
    simp only [Renaming.atExp, checkAtExp, nr_lookupVal]
    rcases C.lookupVal lc with _ | ⟨σ, st⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_genAt h]
  | .op o inst τ => by
    simp only [Renaming.atExp, checkAtExp]
    cases ho : OTstat o with
    | none => rfl
    | some p =>
      obtain ⟨σ, st⟩ := p
      simp only [nr_tys]
      conv => lhs; rw [← nr_OTstat h ho]
      rw [nr_genAt h]
  | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [Renaming.atExp, checkAtExp, nr_checkExp h C e1, nr_checkExp h C e2, nr_checkExpOpt h C e3]
  | .nil τ => by simp only [Renaming.atExp, checkAtExp]; exact nr_isListTy h τ
  | .record row => by simp only [Renaming.atExp, checkAtExp]; exact nr_checkExpRowOpt h C row
  | .update x inst τ row => by
    simp only [Renaming.atExp, checkAtExp, nr_lookupVal, nr_isRecordTy, nr_checkExpRow h C row,
      nr_expRow_row h, nr_recordRow, nr_subB h]
    rcases C.lookupVal ⟨none, x⟩ with _ | ⟨σ, st⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_genAt h]
  | .letE d e => by
    simp only [Renaming.atExp, checkAtExp, nr_checkDec h C d, nr_dec_result h, nr_plusVE, nr_checkExp h _ e]
  | .paren e => by simp only [Renaming.atExp, checkAtExp]; exact nr_checkExp h C e
theorem nr_checkExpRow (h : NR ρ) (C : Ctx) : (r : AExpRow) → checkExpRow ((nr ρ).ctx C) ((nr ρ).expRow r) = checkExpRow C r
  | .field _ e rest => by
    simp only [Renaming.expRow, checkExpRow, nr_checkExp h C e, nr_checkExpRowOpt h C rest]
theorem nr_checkExpRowOpt (h : NR ρ) (C : Ctx) : (r : Option AExpRow) →
    checkExpRowOpt ((nr ρ).ctx C) ((nr ρ).expRowOpt r) = checkExpRowOpt C r
  | none => rfl
  | some r => by simp only [Renaming.expRowOpt, checkExpRowOpt]; exact nr_checkExpRow h C r
theorem nr_checkExp (h : NR ρ) (C : Ctx) : (e : AExp) → checkExp ((nr ρ).ctx C) ((nr ρ).exp e) = checkExp C e
  | .atexp a => by simp only [Renaming.exp, checkExp]; exact nr_checkAtExp h C a
  | .app e a => by
    simp only [Renaming.exp, checkExp, nr_checkExp h C e, nr_checkAtExp h C a, nr_exp_ty h, nr_atExp_ty h]
    congr 1
    generalize AExp.ty e = τ
    cases τ <;> simp [nr_ty_eq_iff h]
  | .lam p e => by
    simp only [Renaming.exp, checkExp, nr_checkAtPat h C p, nr_atPat_ve h, nr_plusVE, nr_checkExp h _ e]
  | .caseE e m => by
    simp only [Renaming.exp, checkExp, nr_checkExp h C e, nr_checkMatch h C m, nr_match_ty h, nr_exp_ty h]
    congr 1
    generalize AMatch.ty m = τ
    cases τ <;> simp [nr_ty_eq_iff h]
theorem nr_checkExpOpt (h : NR ρ) (C : Ctx) : (e : Option AExp) → checkExpOpt ((nr ρ).ctx C) ((nr ρ).expOpt e) = checkExpOpt C e
  | none => rfl
  | some e => by simp only [Renaming.expOpt, checkExpOpt]; exact nr_checkExp h C e
theorem nr_checkMatch (h : NR ρ) (C : Ctx) : (m : AMatch) → checkMatch ((nr ρ).ctx C) ((nr ρ).match_ m) = checkMatch C m
  | .mk mr rest => by
    simp only [Renaming.match_, checkMatch, nr_checkMRule h C mr, nr_mrule_ty h, nr_checkMatchOptAt h C]
theorem nr_checkMatchOptAt (h : NR ρ) (C : Ctx) (τ : Ty) : (m : Option AMatch) →
    checkMatchOptAt ((nr ρ).ctx C) ((nr ρ).ty τ) ((nr ρ).matchOpt m) = checkMatchOptAt C τ m
  | none => rfl
  | some m => by
    simp only [Renaming.matchOpt, checkMatchOptAt, nr_checkMatch h C m, nr_match_ty h, nr_dec_ty h]
theorem nr_checkMRule (h : NR ρ) (C : Ctx) : (mr : AMRule) → checkMRule ((nr ρ).ctx C) ((nr ρ).mrule mr) = checkMRule C mr
  | .mk p e => by
    simp only [Renaming.mrule, checkMRule, nr_checkPat h C p, nr_pat_ve h, nr_plusVE, nr_checkExp h _ e]
theorem nr_checkDec (h : NR ρ) (C : Ctx) : (d : ADec) → checkDec ((nr ρ).ctx C) ((nr ρ).dec d) = checkDec C d
  | .val VE vb => by
    simp only [Renaming.dec, checkDec, nr_plusVE, nr_checkValBind h _ vb, nr_valBind_ve h, nr_valEnv_dec h]
theorem nr_checkValBind (h : NR ρ) (C : Ctx) : (vb : AValBind) → checkValBind ((nr ρ).ctx C) ((nr ρ).valBind vb) = checkValBind C vb
  | .var _ ann τ e rest => by
    simp only [Renaming.valBind, checkValBind, nr_checkAnn h, nr_ann_annU, nr_plusU, nr_checkExp h _ e,
      nr_exp_ty h, nr_dec_ty h, nr_checkValBindOpt h C rest]
  | .pat p e => by
    simp only [Renaming.valBind, checkValBind, nr_checkAtPat h C p, nr_checkExp h C e, nr_exp_ty h,
      nr_atPat_ty h, nr_dec_ty h]
theorem nr_checkValBindOpt (h : NR ρ) (C : Ctx) : (vb : Option AValBind) →
    checkValBindOpt ((nr ρ).ctx C) ((nr ρ).valBindOpt vb) = checkValBindOpt C vb
  | none => rfl
  | some vb => by simp only [Renaming.valBindOpt, checkValBindOpt]; exact nr_checkValBind h C vb
end

end

end StandardElm.Stat
