/-
  A Standard Definition of Elm? Mechanisation: the checker is sound, plan step 9 (section
  "Theorems", group 2, decision D10). `checkExp C a = true` gives a derivation of
  `C ⊢ erase a ⇒ ty a` by the rules of Chapter 4, and likewise for every phrase class;
  `checkModule_sound` gives a derivation of `B ⊢ erase a ⇒ B', E` by the rules of Chapter 5. By
  structural induction on the annotated phrase, each node's checks giving the premises of its rule.
-/
import StandardElmMech.Stat.Annotated

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTopDec)

theorem isConTy_spec {τ : Ty} (h : isConTy τ = true) : ∃ τs t, τ = .con τs t := by
  cases τ <;> simp [isConTy] at h; exact ⟨_, _, rfl⟩

theorem isListTy_spec {τ : Ty} (h : isListTy τ = true) : ∃ τ0, τ = listTy τ0 := by
  match τ, h with
  | .con [τ0] t, h => simp only [isListTy, beq_iff_eq] at h; subst h; exact ⟨τ0, rfl⟩

theorem isRecordTy_spec {τ : Ty} (h : isRecordTy τ = true) : ∃ ρ tl, τ = .record ρ tl := by
  cases τ <;> simp [isRecordTy] at h; exact ⟨_, _, rfl⟩

theorem fn_of_match {τ0 τa : Ty}
    (h : (match τ0 with
      | .fn τ' _ => decide (τ' = τa)
      | _ => false) = true) : ∃ τ, τ0 = .fn τa τ := by
  split at h
  · simp only [decide_eq_true_eq] at h; subst h; exact ⟨_, rfl⟩
  · cases h

/-! ## Patterns -/

mutual
theorem checkAtPat_sound (C : Ctx) : (p : AAtPat) → checkAtPat C p = true → ElAtPat C p.erase p.ve p.ty
  | .wild τ, _ => by simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]; exact .r_s_atpat_wild
  | .scon sc τ, h => by
    simp only [checkAtPat, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
    exact .r_s_atpat_scon (gen_of_genAt h.1) h.2
  | .var x τ, _ => by simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]; exact .r_s_atpat_var
  | .con lc inst τ, h => by
    simp only [checkAtPat] at h
    split at h
    · rename_i σ hl
      simp only [Bool.and_eq_true] at h
      obtain ⟨τs, t, rfl⟩ := isConTy_spec h.2
      simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
      exact .r_s_atpat_con hl (gen_of_genAt h.1)
    · cases h
  | .unit, _ => by simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]; exact .r_s_atpat_unit
  | .tuple p1 p2 p3, h => by
    simp only [checkAtPat, Bool.and_eq_true] at h
    simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
    exact .r_s_atpat_tuple (checkPat_sound C p1 h.1.1) (checkPat_sound C p2 h.1.2) (checkPatOpt_sound C p3 h.2)
  | .nil τ, h => by
    simp only [checkAtPat] at h
    obtain ⟨τ0, rfl⟩ := isListTy_spec h
    simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
    exact .r_s_atpat_nil
  | .record row τ, h => by
    simp only [checkAtPat, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ρτ, tl, rfl⟩ := isRecordTy_spec h2
    simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
    exact .r_s_atpat_record (checkPatRowOpt_sound C row h1) rfl ((Row.subB_iff _ _).mp h3)
  | .paren p, h => by
    simp only [checkAtPat] at h
    simp only [AAtPat.erase, AAtPat.ve, AAtPat.ty]
    exact .r_s_atpat_paren (checkPat_sound C p h)
theorem checkPatRow_sound (C : Ctx) : (r : APatRow) → checkPatRow C r = true → ElPatRow C r.erase r.ve r.row
  | .field l τ rest, h => by
    simp only [checkPatRow] at h
    simp only [APatRow.erase, APatRow.ve, APatRow.row]
    exact .r_s_patrow (checkPatRowOpt_sound C rest h)
theorem checkPatRowOpt_sound (C : Ctx) : (r : Option APatRow) → checkPatRowOpt C r = true →
    ElPatRowOpt C (APatRow.eraseOpt r) (APatRow.veOpt r) (APatRow.rowOpt r)
  | none, _ => by simp only [APatRow.eraseOpt, APatRow.veOpt, APatRow.rowOpt]; exact .opt_none
  | some r, h => by
    simp only [checkPatRowOpt] at h
    simp only [APatRow.eraseOpt, APatRow.veOpt, APatRow.rowOpt]
    exact .opt_some (checkPatRow_sound C r h)
theorem checkPat_sound (C : Ctx) : (p : APat) → checkPat C p = true → ElPat C p.erase p.ve p.ty
  | .atpat a, h => by
    simp only [checkPat] at h
    simp only [APat.erase, APat.ve, APat.ty]
    exact .r_s_pat_atpat (checkAtPat_sound C a h)
  | .con lc inst args τ, h => by
    simp only [checkPat, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h1
    · rename_i σ hl
      simp only [Bool.and_eq_true] at h1
      obtain ⟨τs', t, rfl⟩ := isConTy_spec h1.2
      simp only [APat.erase, APat.ve, APat.ty]
      exact .r_s_pat_con hl (gen_of_genAt h1.1) (checkAtPatList_sound C args h2)
    · cases h1
  | .cons p1 p2, h => by
    simp only [checkPat, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e2 := checkPat_sound C p2 h2
    rw [h3] at e2
    simp only [APat.erase, APat.ve, APat.ty]
    exact .r_s_pat_cons (checkPat_sound C p1 h1) e2
  | .as p x, h => by
    simp only [checkPat] at h
    simp only [APat.erase, APat.ve, APat.ty]
    exact .r_s_pat_as (checkPat_sound C p h)
theorem checkPatOpt_sound (C : Ctx) : (p : Option APat) → checkPatOpt C p = true →
    ElPatOpt C (APat.eraseOpt p) (APat.veOpt p) (APat.tyOpt p)
  | none, _ => by simp only [APat.eraseOpt, APat.veOpt, APat.tyOpt]; exact .opt_none
  | some p, h => by
    simp only [checkPatOpt] at h
    simp only [APat.eraseOpt, APat.veOpt, APat.tyOpt]
    exact .opt_some (checkPat_sound C p h)
theorem checkAtPatList_sound (C : Ctx) : (as : List AAtPat) → checkAtPatList C as = true →
    ElAtPatList C (AAtPat.eraseList as) (AAtPat.veList as) (AAtPat.tyList as)
  | [], _ => by simp only [AAtPat.eraseList, AAtPat.veList, AAtPat.tyList]; exact .seq_nil
  | a :: as, h => by
    simp only [checkAtPatList, Bool.and_eq_true] at h
    simp only [AAtPat.eraseList, AAtPat.veList, AAtPat.tyList]
    exact .seq_cons (checkAtPat_sound C a h.1) (checkAtPatList_sound C as h.2)
end

/-! ## Expressions -/

theorem checkAnn_sound (C : Ctx) (ann : Option (BTy × List BVar)) (τ : Ty) (h : checkAnn C ann τ = true) :
    AnnOK C (ann.map Prod.fst) (annU ann) τ := by
  match ann, h with
  | none, _ => exact .opt_none
  | some (ty, U'), h =>
    simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact .opt_some ((newForB_iff _ _ _).mp h1) (elabTy_sound _ _ _ h2) h3

theorem lookup_gen {C : Ctx} {lv : LongId} {inst : List Ty} {τ : Ty}
    (h : (match C.lookupVal lv with
      | some (σ, _) => genAt σ inst τ
      | none => false) = true) : ∃ σ is, C.lookupVal lv = some (σ, is) ∧ Gen σ τ := by
  split at h
  · rename_i σ is hl; exact ⟨σ, is, hl, gen_of_genAt h⟩
  · cases h

mutual
theorem checkAtExp_sound (C : Ctx) : (a : AAtExp) → checkAtExp C a = true → ElAtExp C a.erase a.ty
  | .scon sc τ, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_scon (gen_of_genAt h)
  | .var lv inst τ, h => by
    simp only [checkAtExp] at h
    obtain ⟨σ, is, hl, hg⟩ := lookup_gen h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_longvar hl hg
  | .con lc inst τ, h => by
    simp only [checkAtExp] at h
    obtain ⟨σ, is, hl, hg⟩ := lookup_gen h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_longcon hl hg
  | .op o inst τ, h => by
    simp only [checkAtExp] at h
    split at h
    · rename_i σ is hl
      simp only [AAtExp.erase, AAtExp.ty]
      exact .r_s_atexp_op hl (gen_of_genAt h)
    · cases h
  | .unit, _ => by simp only [AAtExp.erase, AAtExp.ty]; exact .r_s_atexp_unit
  | .tuple e1 e2 e3, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_tuple (checkExp_sound C e1 h.1.1) (checkExp_sound C e2 h.1.2) (checkExpOpt_sound C e3 h.2)
  | .nil τ, h => by
    simp only [checkAtExp] at h
    obtain ⟨τ0, rfl⟩ := isListTy_spec h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_nil
  | .record row, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_record (checkExpRowOpt_sound C row h)
  | .update x inst τ row, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨σ, is, hl, hg⟩ := lookup_gen h1
    obtain ⟨ρτ, tl, rfl⟩ := isRecordTy_spec h2
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_update (.r_s_atexp_longvar hl hg) rfl (checkExpRow_sound C row h3)
      ((Row.subB_iff _ _).mp h4)
  | .letE d e, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_let (checkDec_sound C d h.1) (checkExp_sound _ e h.2)
  | .paren e, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, AAtExp.ty]
    exact .r_s_atexp_paren (checkExp_sound C e h)
theorem checkExpRow_sound (C : Ctx) : (r : AExpRow) → checkExpRow C r = true → ElExpRow C r.erase r.row
  | .field l e rest, h => by
    simp only [checkExpRow, Bool.and_eq_true] at h
    simp only [AExpRow.erase, AExpRow.row]
    exact .r_s_exprow (checkExp_sound C e h.1) (checkExpRowOpt_sound C rest h.2)
theorem checkExpRowOpt_sound (C : Ctx) : (r : Option AExpRow) → checkExpRowOpt C r = true →
    ElExpRowOpt C (AExpRow.eraseOpt r) (AExpRow.rowOpt r)
  | none, _ => by simp only [AExpRow.eraseOpt, AExpRow.rowOpt]; exact .opt_none
  | some r, h => by
    simp only [checkExpRowOpt] at h
    simp only [AExpRow.eraseOpt, AExpRow.rowOpt]
    exact .opt_some (checkExpRow_sound C r h)
theorem checkExp_sound (C : Ctx) : (a : AExp) → checkExp C a = true → ElExp C a.erase a.ty
  | .atexp a, h => by
    simp only [checkExp] at h
    simp only [AExp.erase, AExp.ty]
    exact .r_s_exp_atexp (checkAtExp_sound C a h)
  | .app e a, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have he := checkExp_sound C e h1
    obtain ⟨τ, hτ⟩ := fn_of_match h3
    rw [hτ] at he
    simp only [AExp.erase, AExp.ty, hτ, Ty.cod]
    exact .r_s_exp_app he (checkAtExp_sound C a h2)
  | .lam p e, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    simp only [AExp.erase, AExp.ty]
    exact .r_s_exp_lambda (checkAtPat_sound C p h.1) (checkExp_sound _ e h.2)
  | .caseE e m, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hm := checkMatch_sound C m h2
    obtain ⟨τ', hτ⟩ := fn_of_match h3
    rw [hτ] at hm
    simp only [AExp.erase, AExp.ty, hτ, Ty.cod]
    exact .r_s_exp_case (checkExp_sound C e h1) hm
theorem checkExpOpt_sound (C : Ctx) : (e : Option AExp) → checkExpOpt C e = true →
    ElExpOpt C (AExp.eraseOpt e) (AExp.tyOpt e)
  | none, _ => by simp only [AExp.eraseOpt, AExp.tyOpt]; exact .opt_none
  | some e, h => by
    simp only [checkExpOpt] at h
    simp only [AExp.eraseOpt, AExp.tyOpt]
    exact .opt_some (checkExp_sound C e h)
theorem checkMatch_sound (C : Ctx) : (m : AMatch) → checkMatch C m = true → ElMatch C m.erase m.ty
  | .mk mr rest, h => by
    simp only [checkMatch, Bool.and_eq_true] at h
    simp only [AMatch.erase, AMatch.ty]
    exact .r_s_match (checkMRule_sound C mr h.1) (checkMatchOptAt_sound C _ rest h.2)
theorem checkMatchOptAt_sound (C : Ctx) (τ : Ty) : (m : Option AMatch) → checkMatchOptAt C τ m = true →
    ElMatchOpt C (AMatch.eraseOpt m) τ
  | none, _ => by simp only [AMatch.eraseOpt]; exact .opt_none
  | some m, h => by
    simp only [checkMatchOptAt, Bool.and_eq_true, decide_eq_true_eq] at h
    have hm := checkMatch_sound C m h.1
    rw [h.2] at hm
    simp only [AMatch.eraseOpt]
    exact .opt_some hm
theorem checkMRule_sound (C : Ctx) : (mr : AMRule) → checkMRule C mr = true → ElMRule C mr.erase mr.ty
  | .mk p e, h => by
    simp only [checkMRule, Bool.and_eq_true] at h
    simp only [AMRule.erase, AMRule.ty]
    exact .r_s_mrule (checkPat_sound C p h.1) (checkExp_sound _ e h.2)
theorem checkDec_sound (C : Ctx) : (d : ADec) → checkDec C d = true → ElDec C d.erase (d.result C)
  | .val VE vb, h => by
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at h
    have hv := checkValBind_sound _ vb h.1
    rw [h.2] at hv
    simp only [ADec.erase, ADec.result]
    exact .r_s_dec_group hv
theorem checkValBind_sound (C : Ctx) : (vb : AValBind) → checkValBind C vb = true → ElValBind C vb.erase vb.ve
  | .var x ann τ e rest, h => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have he := checkExp_sound _ e h2
    rw [h3] at he
    have hr := checkValBindOpt_sound C rest h4
    have hv := ElValBind.r_s_valbind_var (x := x) (checkAnn_sound C ann τ h1) he hr
    simp only [Option.isSome_map] at hv
    simp only [AValBind.erase, AValBind.ve]
    cases rest <;> exact hv
  | .pat p e, h => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have he := checkExp_sound C e h2
    rw [h3] at he
    simp only [AValBind.erase]
    exact .r_s_valbind_pat (checkAtPat_sound C p h1) he
theorem checkValBindOpt_sound (C : Ctx) : (vb : Option AValBind) → checkValBindOpt C vb = true →
    ElValBindOpt C (AValBind.eraseOpt vb) (AValBind.veOpt vb)
  | none, _ => by simp only [AValBind.eraseOpt, AValBind.veOpt]; exact .opt_none
  | some vb, h => by
    simp only [checkValBindOpt] at h
    simp only [AValBind.eraseOpt, AValBind.veOpt]
    exact .opt_some (checkValBind_sound C vb h)
end

/-! ## Modules -/

mutual
theorem portB_sound : (τ : Ty) → portB τ = true → Port τ
  | .con [] t, h => by
    simp only [portB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (((((h | h) | h) | h) | h) | h) | h <;> subst h
    · exact .int
    · exact .float
    · exact .bool
    · exact .string
    · exact .bytes
    · exact .unit
    · exact .value
  | .con [τ] t, h => by
    simp only [portB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨(h | h) | h, h2⟩ := h <;> subst h
    · exact .list (portB_sound τ h2)
    · exact .maybe (portB_sound τ h2)
    · exact .array (portB_sound τ h2)
  | .con [τ1, τ2] t, h => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    exact .tuple2 (portB_sound τ1 h1) (portB_sound τ2 h2)
  | .con [τ1, τ2, τ3] t, h => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩ := h
    exact .tuple3 (portB_sound τ1 h1) (portB_sound τ2 h2) (portB_sound τ3 h3)
  | .record ρ none, h => by
    simp only [portB] at h
    exact .record (portRowB_sound ρ h)
  | .con (_ :: _ :: _ :: _ :: _) _, h => by simp [portB] at h
  | .record _ (some _), h => by simp [portB] at h
  | .var _, h => by simp [portB] at h
  | .fn _ _, h => by simp [portB] at h
theorem portRowB_sound : (ρ : Row) → portRowB ρ = true → ∀ l τ, (l, τ) ∈ ρ → Port τ
  | [], _, l, τ, hm => by cases hm
  | (l', τ') :: rest, h, l, τ, hm => by
    simp only [portRowB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with e | e
    · cases e; exact portB_sound τ' h.1
    · exact portRowB_sound rest h.2 l τ e
end

theorem elabPort_sound (C : Ctx) (x : Var) (ty : BTy) (U : List BVar) (E : Env) (PE : PortEnv)
    (h : elabPort C x ty U = some (E, PE)) : ElTopDec C (.port x ty) E PE := by
  unfold elabPort at h
  split at h
  · rename_i hn
    have hnew := (newForB_iff _ _ _).mp hn
    split at h
    · rename_i τ' α t hτ
      have hel := elabTy_sound _ _ _ hτ
      split at h
      · rename_i hc
        obtain ⟨rfl, hp⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .r_sm_topdec_portout hnew hel rfl (portB_sound _ hp)
      · split at h
        · rename_i τ'' α'
          split at h
          · rename_i hc
            obtain ⟨rfl, rfl, hp⟩ := hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .r_sm_topdec_portin hnew hel rfl (portB_sound _ hp)
          · cases h
        · cases h
    · cases h
  · cases h

theorem splitShape_spec {d1 d2 : BTopDec} (h : splitShape d1 d2 = true) :
    ∃ db tbs1 tbs2, d1 = .types db tbs1 ∧ d2 = .types none tbs2 ∧ (db.isSome ∨ tbs1 ≠ []) ∧ tbs2 ≠ [] := by
  match d1, d2, h with
  | .types db tbs1, .types none tbs2, h =>
    simp only [splitShape, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at h
    refine ⟨db, tbs1, tbs2, rfl, rfl, ?_, h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl h1
    · exact .inr h1

theorem checkTopDec_sound (C : Ctx) : (a : ATopDec) → (E : Env) → (PE : PortEnv) →
    checkTopDec C a = some (E, PE) → ElTopDec C a.erase E PE
  | .value VE vb, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := checkValBind_sound _ vb hc.1
      rw [hc.2] at hv
      exact .r_sm_topdec_value hv
    · cases h
  | .types TE VE db tbs, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .r_sm_topdec_types (checkTypes_sound C TE VE db tbs hc)
    · cases h
  | .typesSplit a1 a2, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hs
      obtain ⟨db, tbs1, tbs2, h1e, h2e, hc1, hc2⟩ := splitShape_spec hs
      split at h
      · rename_i E1 PE1 h1
        split at h
        · rename_i E2 PE2 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have d1 := checkTopDec_sound C a1 E1 PE1 h1
          have d2 := checkTopDec_sound _ a2 E2 PE2 h2
          rw [h1e] at d1
          rw [h2e] at d2
          have : (ATopDec.typesSplit a1 a2).erase = .types db (tbs1 ++ tbs2) := by
            simp only [ATopDec.erase, h1e, h2e]
          rw [this]
          exact .r_sm_topdec_seq_types hc1 hc2 d1 d2
        · cases h
      · cases h
    · cases h
  | .port x ty U, E, PE, h => by
    simp only [checkTopDec] at h
    exact elabPort_sound C x ty U E PE h
  | .seq a1 a2, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i E1 PE1 h1
      split at h
      · rename_i E2 PE2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .r_sm_topdec_seq (checkTopDec_sound C a1 E1 PE1 h1) (checkTopDec_sound _ a2 E2 PE2 h2)
      · cases h
    · cases h

theorem checkTopDecOpt_sound (C : Ctx) (a : Option ATopDec) (E : Env) (PE : PortEnv)
    (h : checkTopDecOpt C a = some (E, PE)) : ElTopDecOpt C (a.map ATopDec.erase) E PE := by
  cases a with
  | none =>
    simp only [checkTopDecOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .opt_none
  | some d => exact .opt_some (checkTopDec_sound C d E PE h)

/-- D10: a certificate that checks is a derivation of r:sm-module. -/
theorem checkModule_sound (B : SBasis) (a : AModule) (B' : SBasis) (E : Env)
    (h : a.result B = some (B', E)) : ElModule B a.erase B' E := by
  unfold AModule.result importCtx at h
  cases hπ : elabImports B π0 (defaultImports ++ a.imports) with
  | none => rw [hπ] at h; cases h
  | some π =>
    rw [hπ] at h
    simp only [Option.map_some] at h
    unfold AModule.resultIn at h
    split at h
    · cases h
    · rename_i E' PE hd
      split at h
      · cases h
      · rename_i I hI
        split at h
        · cases h
        · rename_i hn
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .r_sm_module (elabImports_sound B _ π0 π hπ) (checkTopDecOpt_sound _ a.body E' PE hd)
            (.r_sm_header hI) hn

end StandardElm.Stat
