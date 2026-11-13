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
    simp only [Renaming.atExp, checkAtExp, nr_checkExpS h C e1, nr_checkExpS h C e2, nr_checkExpOpt h C e3]
  | .nil τ => by simp only [Renaming.atExp, checkAtExp]; exact nr_isListTy h τ
  | .record row => by simp only [Renaming.atExp, checkAtExp]; exact nr_checkExpRowOpt h C row
  | .update x inst τ row => by
    simp only [Renaming.atExp, checkAtExp, nr_lookupVal, nr_isRecordTy, nr_checkExpRow h C row,
      nr_expRow_row h, nr_recordRow, nr_subB h]
    rcases C.lookupVal ⟨none, x⟩ with _ | ⟨σ, st⟩
    · rfl
    · simp only [Option.map_some, nr_tys, nr_genAt h]
  | .letE d e => by
    simp only [Renaming.atExp, checkAtExp, nr_checkDec h C d, nr_dec_result h, nr_plusVE, nr_checkExpS h _ e]
  | .paren e => by simp only [Renaming.atExp, checkAtExp]; exact nr_checkExpS h C e
theorem nr_checkExpRow (h : NR ρ) (C : Ctx) : (r : AExpRow) → checkExpRow ((nr ρ).ctx C) ((nr ρ).expRow r) = checkExpRow C r
  | .field _ e rest => by
    simp only [Renaming.expRow, checkExpRow, nr_checkExpS h C e, nr_checkExpRowOpt h C rest]
theorem nr_checkExpRowOpt (h : NR ρ) (C : Ctx) : (r : Option AExpRow) →
    checkExpRowOpt ((nr ρ).ctx C) ((nr ρ).expRowOpt r) = checkExpRowOpt C r
  | none => rfl
  | some r => by simp only [Renaming.expRowOpt, checkExpRowOpt]; exact nr_checkExpRow h C r
theorem nr_checkExpS (h : NR ρ) (C : Ctx) : (e : AExp) → checkExpS ((nr ρ).ctx C) ((nr ρ).exp e) = checkExpS C e
  | .atexp a => by simp only [Renaming.exp, checkExpS]; exact nr_checkAtExp h C a
  | .app e a => by
    simp only [Renaming.exp, checkExpS, nr_checkExpS h C e, nr_checkAtExp h C a, nr_exp_ty h, nr_atExp_ty h]
    congr 1
    generalize AExp.ty e = τ
    cases τ <;> simp [nr_ty_eq_iff h]
  | .lam p e => by
    simp only [Renaming.exp, checkExpS, nr_checkAtPat h C p, nr_atPat_ve h, nr_plusVE, nr_checkExpS h _ e]
  | .caseE e m => by
    simp only [Renaming.exp, checkExpS, nr_checkExpS h C e, nr_checkMatch h C m, nr_match_ty h, nr_exp_ty h]
    congr 1
    generalize AMatch.ty m = τ
    cases τ <;> simp [nr_ty_eq_iff h]
theorem nr_checkExpOpt (h : NR ρ) (C : Ctx) : (e : Option AExp) → checkExpOpt ((nr ρ).ctx C) ((nr ρ).expOpt e) = checkExpOpt C e
  | none => rfl
  | some e => by simp only [Renaming.expOpt, checkExpOpt]; exact nr_checkExpS h C e
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
    simp only [Renaming.mrule, checkMRule, nr_checkPat h C p, nr_pat_ve h, nr_plusVE, nr_checkExpS h _ e]
theorem nr_checkDec (h : NR ρ) (C : Ctx) : (d : ADec) → checkDec ((nr ρ).ctx C) ((nr ρ).dec d) = checkDec C d
  | .val VE vb => by
    simp only [Renaming.dec, checkDec, nr_plusVE, nr_checkValBind h _ vb, nr_valBind_ve h, nr_valEnv_dec h]
theorem nr_checkValBind (h : NR ρ) (C : Ctx) : (vb : AValBind) → checkValBind ((nr ρ).ctx C) ((nr ρ).valBind vb) = checkValBind C vb
  | .var _ ann τ e rest => by
    simp only [Renaming.valBind, checkValBind, nr_checkAnn h, nr_ann_annU, nr_plusU, nr_checkExpS h _ e,
      nr_exp_ty h, nr_dec_ty h, nr_checkValBindOpt h C rest]
  | .pat p e => by
    simp only [Renaming.valBind, checkValBind, nr_checkAtPat h C p, nr_checkExpS h C e, nr_exp_ty h,
      nr_atPat_ty h, nr_dec_ty h]
theorem nr_checkValBindOpt (h : NR ρ) (C : Ctx) : (vb : Option AValBind) →
    checkValBindOpt ((nr ρ).ctx C) ((nr ρ).valBindOpt vb) = checkValBindOpt C vb
  | none => rfl
  | some vb => by simp only [Renaming.valBindOpt, checkValBindOpt]; exact nr_checkValBind h C vb
end

/-! ## Nodes -/

mutual
theorem renameNames_nr : (τ : Ty) → Ty.renameNames ρ τ = (nr ρ).ty τ
  | .var _ => rfl
  | .record r tl => by simp only [Ty.renameNames, nr_ty_record, renameRow_nr r]
  | .fn a b => by simp only [Ty.renameNames, nr_ty_fn, renameNames_nr a, renameNames_nr b]
  | .con as t => by
    simp only [Ty.renameNames, renameName_eq, renameList_nr as, nr_tys, nr_ty_con]
    rfl
theorem renameRow_nr : (r : Row) → Ty.renameRow ρ r = (nr ρ).row r
  | [] => rfl
  | (l, τ) :: rest => by simp only [Ty.renameRow, renameNames_nr τ, renameRow_nr rest, nr_row_cons]
theorem renameList_nr : (l : List Ty) → Ty.renameList ρ l = (nr ρ).tys l
  | [] => rfl
  | τ :: rest => by simp only [Ty.renameList, renameNames_nr τ, renameList_nr rest, Renaming.tys]
end

/-- A node renamed. -/
theorem node_renameNames (n : Node) :
    n.renameNames ρ = ⟨n.path, n.U, n.tys.map (nr ρ).ty, n.schemes.map (nr ρ).scheme⟩ := by
  simp only [Node.renameNames]
  congr 1
  · exact List.map_congr_left fun τ _ => renameNames_nr τ
  · exact List.map_congr_left fun σ _ => by simp [Renaming.scheme, renameNames_nr]

@[simp] theorem nr_veSchemes (VE : ValEnv) : veSchemes ((nr ρ).valEnv VE) = (veSchemes VE).map (nr ρ).scheme := by
  simp [veSchemes, Renaming.valEnv]

/-- `ns.map (Node.renameNames ρ)`, the nodes renamed. -/
abbrev nrNodes (ρ : List (TyName × TyName)) (ns : List Node) : List Node := ns.map (Node.renameNames ρ)

theorem nrNode_mk (p : List Nat) (U : List BVar) (ts : List Ty) (ss : List Scheme) :
    Node.renameNames ρ ⟨p, U, ts, ss⟩ = ⟨p, U, ts.map (nr ρ).ty, ss.map (nr ρ).scheme⟩ := node_renameNames _

mutual
theorem nr_nodesAtPat (h : NR ρ) (U : List BVar) (path : List Nat) : (p : AAtPat) →
    nodesAtPat U path ((nr ρ).atPat p) = nrNodes ρ (nodesAtPat U path p)
  | .wild τ | .scon _ τ | .var _ τ | .nil τ => by
    simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, Renaming.valEnv, mono, Renaming.scheme]
  | .con lc inst τ => by
    simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, nr_tys]
  | .unit => by simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, nr_tUnitTy h]
  | .tuple p1 p2 p3 => by
    have e1 := nr_atPat_ty h (.tuple p1 p2 p3)
    have e2 := nr_atPat_ve h (.tuple p1 p2 p3)
    simp only [Renaming.atPat, AAtPat.ty] at e1 e2
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, nr_nodesPatOpt h, e2, nr_veSchemes, nr_pat_ty h, nr_patOpt_ty h, nr_tupleTy h]
  | .record row τ => by
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPatRowOpt h, nr_patRowOpt_ve h, nr_veSchemes]
  | .paren p => by
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, nr_pat_ty h, nr_pat_ve h, nr_veSchemes]
theorem nr_nodesPatRow (h : NR ρ) (U : List BVar) (path : List Nat) : (r : APatRow) →
    nodesPatRow U path ((nr ρ).patRow r) = nrNodes ρ (nodesPatRow U path r)
  | .field l τ rest => by
    have e1 := nr_patRow_row (ρ := ρ) (.field l τ rest)
    simp only [Renaming.patRow] at e1
    simp only [Renaming.patRow, nodesPatRow, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPatRowOpt h, e1, nr_row_map, List.map_map]
    rfl
theorem nr_nodesPatRowOpt (h : NR ρ) (U : List BVar) (path : List Nat) : (r : Option APatRow) →
    nodesPatRowOpt U path ((nr ρ).patRowOpt r) = nrNodes ρ (nodesPatRowOpt U path r)
  | none => rfl
  | some r => by simp only [Renaming.patRowOpt, nodesPatRowOpt]; exact nr_nodesPatRow h U path r
theorem nr_nodesPat (h : NR ρ) (U : List BVar) (path : List Nat) : (p : APat) →
    nodesPat U path ((nr ρ).pat p) = nrNodes ρ (nodesPat U path p)
  | .atpat a => by
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesAtPat h, nr_atPat_ty h, nr_atPat_ve h, nr_veSchemes]
  | .con lc inst args τ => by
    have e2 := nr_pat_ve h (.con lc inst args τ)
    simp only [Renaming.pat, nr_tys] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesAtPats h, e2, nr_veSchemes, nr_tys]
  | .cons p1 p2 => by
    have e2 := nr_pat_ve h (.cons p1 p2)
    simp only [Renaming.pat] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, e2, nr_veSchemes, nr_pat_ty h, nr_listTy h]
  | .as p x => by
    have e2 := nr_pat_ve h (.as p x)
    simp only [Renaming.pat] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, e2, nr_veSchemes, nr_pat_ty h]
theorem nr_nodesPatOpt (h : NR ρ) (U : List BVar) (path : List Nat) : (p : Option APat) →
    nodesPatOpt U path ((nr ρ).patOpt p) = nrNodes ρ (nodesPatOpt U path p)
  | none => rfl
  | some p => by simp only [Renaming.patOpt, nodesPatOpt]; exact nr_nodesPat h U path p
theorem nr_nodesAtPats (h : NR ρ) (U : List BVar) (path : List Nat) : (i : Nat) → (ps : List AAtPat) →
    nodesAtPats U path i ((nr ρ).atPats ps) = nrNodes ρ (nodesAtPats U path i ps)
  | _, [] => rfl
  | i, p :: ps => by
    simp only [Renaming.atPats, nodesAtPats, List.map_append, nr_nodesAtPat h, nr_nodesAtPats h U path (i + 1) ps]
end

theorem nr_nodesE_head (C : Ctx) (path : List Nat) (τ : Ty) (ts : List Ty) :
    Node.renameNames ρ ⟨path, C.U, τ :: ts, []⟩ = ⟨path, ((nr ρ).ctx C).U, (nr ρ).ty τ :: ts.map (nr ρ).ty, []⟩ := by
  rw [nrNode_mk]; simp

mutual
theorem nr_nodesAtExp (h : NR ρ) (C : Ctx) (path : List Nat) : (a : AAtExp) →
    nodesAtExp ((nr ρ).ctx C) path ((nr ρ).atExp a) = nrNodes ρ (nodesAtExp C path a)
  | .scon sc τ => by
    simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_litInst]
  | .var lv inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .con lc inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .op o inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .unit => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tUnitTy h]
  | .nil τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk]
  | .tuple e1 e2 e3 => by
    have e := nr_atExp_ty h (.tuple e1 e2 e3)
    simp only [Renaming.atExp] at e
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e, nr_nodesExp h, nr_nodesExpOpt h]
  | .record row => by
    have e := nr_atExp_ty h (.record row)
    simp only [Renaming.atExp] at e
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e, nr_nodesExpRowOpt h]
  | .update x inst τ row => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_nodesExpRow h, nr_tys]
  | .letE d e => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_exp_ty h, nr_nodesDec h, nr_dec_result h, nr_plusVE, nr_nodesExp h]
  | .paren e => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_exp_ty h, nr_nodesExp h]
theorem nr_nodesExpRow (h : NR ρ) (C : Ctx) (path : List Nat) : (r : AExpRow) →
    nodesExpRow ((nr ρ).ctx C) path ((nr ρ).expRow r) = nrNodes ρ (nodesExpRow C path r)
  | .field l e rest => by
    have e1 := nr_expRow_row h (.field l e rest)
    simp only [Renaming.expRow] at e1
    simp only [Renaming.expRow, nodesExpRow, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesExpRowOpt h, nr_row_map, List.map_map]
    rfl
theorem nr_nodesExpRowOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (r : Option AExpRow) →
    nodesExpRowOpt ((nr ρ).ctx C) path ((nr ρ).expRowOpt r) = nrNodes ρ (nodesExpRowOpt C path r)
  | none => rfl
  | some r => by simp only [Renaming.expRowOpt, nodesExpRowOpt]; exact nr_nodesExpRow h C path r
theorem nr_nodesExp (h : NR ρ) (C : Ctx) (path : List Nat) : (e : AExp) →
    nodesExp ((nr ρ).ctx C) path ((nr ρ).exp e) = nrNodes ρ (nodesExp C path e)
  | .atexp a => by
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_atExp_ty h, nr_nodesAtExp h]
  | .app e a => by
    have e1 := nr_exp_ty h (.app e a)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesAtExp h]
  | .lam p e => by
    have e1 := nr_exp_ty h (.lam p e)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesAtPat h, nr_atPat_ve h, nr_plusVE, nr_nodesExp h]
  | .caseE e m => by
    have e1 := nr_exp_ty h (.caseE e m)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesMatch h]
theorem nr_nodesExpOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (e : Option AExp) →
    nodesExpOpt ((nr ρ).ctx C) path ((nr ρ).expOpt e) = nrNodes ρ (nodesExpOpt C path e)
  | none => rfl
  | some e => by simp only [Renaming.expOpt, nodesExpOpt]; exact nr_nodesExp h C path e
theorem nr_nodesMatch (h : NR ρ) (C : Ctx) (path : List Nat) : (m : AMatch) →
    nodesMatch ((nr ρ).ctx C) path ((nr ρ).match_ m) = nrNodes ρ (nodesMatch C path m)
  | .mk (.mk p e) rest => by
    have e1 := nr_mrule_ty h (.mk p e)
    simp only [Renaming.mrule] at e1
    simp only [Renaming.match_, Renaming.mrule, nodesMatch, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_ctx_U, e1, nr_nodesPat h, nr_pat_ve h, nr_plusVE, nr_nodesExp h, nr_nodesMatchOpt h]
theorem nr_nodesMatchOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (m : Option AMatch) →
    nodesMatchOpt ((nr ρ).ctx C) path ((nr ρ).matchOpt m) = nrNodes ρ (nodesMatchOpt C path m)
  | none => rfl
  | some m => by simp only [Renaming.matchOpt, nodesMatchOpt]; exact nr_nodesMatch h C path m
theorem nr_nodesDec (h : NR ρ) (C : Ctx) (path : List Nat) : (d : ADec) →
    nodesDec ((nr ρ).ctx C) path ((nr ρ).dec d) = nrNodes ρ (nodesDec C path d)
  | .val VE vb => by
    simp only [Renaming.dec, nodesDec, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_ctx_tyvars h, nr_closGroup h, nr_veSchemes, nr_plusVE, nr_nodesValBind h]
theorem nr_nodesValBind (h : NR ρ) (C : Ctx) (path : List Nat) : (vb : AValBind) →
    nodesValBind ((nr ρ).ctx C) path ((nr ρ).valBind vb) = nrNodes ρ (nodesValBind C path vb)
  | .var x ann τ e rest => by
    have e1 := nr_valBind_ve h (.var x ann τ e rest)
    simp only [Renaming.valBind] at e1
    simp only [Renaming.valBind, nodesValBind, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_veSchemes, nr_ann_annU, nr_plusU, nr_nodesExp h, nr_nodesValBindOpt h]
  | .pat p e => by
    simp only [Renaming.valBind, nodesValBind, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_atPat_ty h, nr_atPat_ve h, nr_veSchemes, nr_nodesAtPat h, nr_nodesExp h]
theorem nr_nodesValBindOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (vb : Option AValBind) →
    nodesValBindOpt ((nr ρ).ctx C) path ((nr ρ).valBindOpt vb) = nrNodes ρ (nodesValBindOpt C path vb)
  | none => rfl
  | some vb => by simp only [Renaming.valBindOpt, nodesValBindOpt]; exact nr_nodesValBind h C path vb
end

/-! A renaming of type names keeps a type `Ty.okB`: it moves no label and no variable. -/

mutual
theorem nr_cnB : (τ : Ty) → cnB ((nr ρ).ty τ) = cnB τ
  | .var _ => rfl
  | .record r tl => by
    simp only [Renaming.ty, cnB, nr_cnRowB r]
    congr 2
    exact nr_labs r
  | .fn a b => by simp only [Renaming.ty, cnB, nr_cnB a, nr_cnB b]
  | .con as t => by simp only [Renaming.ty, cnB, nr_cnListB as]
theorem nr_cnRowB : (r : Row) → cnRowB ((nr ρ).row r) = cnRowB r
  | [] => rfl
  | (l, τ) :: rest => by simp only [Renaming.row, cnRowB, nr_cnB τ, nr_cnRowB rest]
theorem nr_cnListB : (l : List Ty) → cnListB ((nr ρ).tys l) = cnListB l
  | [] => rfl
  | τ :: rest => by simp only [Renaming.tys, cnListB, nr_cnB τ, nr_cnListB rest]
theorem nr_labs : (r : Row) → labs ((nr ρ).row r) = labs r
  | [] => rfl
  | (l, τ) :: rest => by simp only [Renaming.row, labs, List.map_cons]; exact congrArg _ (nr_labs rest)
end

theorem nr_okB (τ : Ty) : Ty.okB ((nr ρ).ty τ) = Ty.okB τ := by
  simp only [Ty.okB, nr_cnB, nr_vars]

theorem nr_nodesOkB (ns : List Node) : nodesOkB (nrNodes ρ ns) = nodesOkB ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [nodesOkB, List.map_cons, List.all_cons] at ih ⊢
    rw [ih, node_renameNames]
    congr 1
    induction n.tys with
    | nil => rfl
    | cons τ ts ih' => simp only [List.map_cons, List.all_cons, nr_okB, ih']

theorem nr_okExpB (h : NR ρ) (e : AExp) : okExpB ((nr ρ).exp e) = okExpB e := by
  rw [← nodesOkB_nodesExp ((nr ρ).ctx Inhabited.default) [], nr_nodesExp h, nr_nodesOkB, nodesOkB_nodesExp]

theorem nr_okValBindB (h : NR ρ) (vb : AValBind) : okValBindB ((nr ρ).valBind vb) = okValBindB vb := by
  rw [← nodesOkB_nodesValBind ((nr ρ).ctx Inhabited.default) [], nr_nodesValBind h, nr_nodesOkB,
    nodesOkB_nodesValBind]

theorem nr_checkExp (h : NR ρ) (C : Ctx) (e : AExp) : checkExp ((nr ρ).ctx C) ((nr ρ).exp e) = checkExp C e := by
  simp only [checkExp, nr_checkExpS h, nr_okExpB h]

end

end StandardElm.Stat
