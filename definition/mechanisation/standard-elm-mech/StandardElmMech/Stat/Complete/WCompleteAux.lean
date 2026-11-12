/-
  A Standard Definition of Elm? Mechanisation: lemmas for the expression part of the main
  induction L11 of plan step 11 (milestone (b), section 8): type expressions (L7: `elabTy` reads
  only `U` and the type constructors), groups (the entries before the members are typed, and the
  value environment they give), the operators' schemes, and the `let` step (L3 then L4: the body's
  context in W, closed, against the derivation's, closed).
-/
import StandardElmMech.Stat.Complete.WCompletePat

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPat BValBind)

/-! ## Type expressions (L7) -/

mutual
theorem elabTy_congr {C1 C2 : Ctx} (hU : C1.U = C2.U) (hT : ∀ lc, C1.lookupTy lc = C2.lookupTy lc) :
    ∀ ty : BTy, elabTy C1 ty = elabTy C2 ty
  | .tyvar a => by simp only [elabTy, hU]
  | .record row => by simp only [elabTy, elabTyRowOpt_congr hU hT row]
  | .openRecord r row => by simp only [elabTy, hU, elabTyRow_congr hU hT row]
  | .unit => rfl
  | .tuple t1 t2 t3 => by
    simp only [elabTy, elabTy_congr hU hT t1, elabTy_congr hU hT t2, elabTyOpt_congr hU hT t3]
  | .con c args => by simp only [elabTy, hT c, elabTyList_congr hU hT args]
  | .fn t1 t2 => by simp only [elabTy, elabTy_congr hU hT t1, elabTy_congr hU hT t2]
  | .paren t => by simp only [elabTy, elabTy_congr hU hT t]
theorem elabTyRow_congr {C1 C2 : Ctx} (hU : C1.U = C2.U) (hT : ∀ lc, C1.lookupTy lc = C2.lookupTy lc) :
    ∀ row : BTyRow, elabTyRow C1 row = elabTyRow C2 row
  | .field l t rest => by simp only [elabTyRow, elabTy_congr hU hT t, elabTyRowOpt_congr hU hT rest]
theorem elabTyRowOpt_congr {C1 C2 : Ctx} (hU : C1.U = C2.U) (hT : ∀ lc, C1.lookupTy lc = C2.lookupTy lc) :
    ∀ row : Option BTyRow, elabTyRowOpt C1 row = elabTyRowOpt C2 row
  | none => rfl
  | some row => by simp only [elabTyRowOpt, elabTyRow_congr hU hT row]
theorem elabTyOpt_congr {C1 C2 : Ctx} (hU : C1.U = C2.U) (hT : ∀ lc, C1.lookupTy lc = C2.lookupTy lc) :
    ∀ ty : Option BTy, elabTyOpt C1 ty = elabTyOpt C2 ty
  | none => rfl
  | some t => by simp only [elabTyOpt, elabTy_congr hU hT t]
theorem elabTyList_congr {C1 C2 : Ctx} (hU : C1.U = C2.U) (hT : ∀ lc, C1.lookupTy lc = C2.lookupTy lc) :
    ∀ l : List BTy, elabTyList C1 l = elabTyList C2 l
  | [] => rfl
  | t :: ts => by simp only [elabTyList, elabTy_congr hU hT t, elabTyList_congr hU hT ts]
end

/-- An annotation without type variables names no explicit variable. -/
theorem newFor_nil {U' : List BVar} {ty : BTy} {CU : List BVar} (h : newForB U' ty CU = true)
    (hn : (bTyNames ty).isEmpty = true) : U' = [] := by
  rw [newForB_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  rw [List.isEmpty_iff] at hn
  cases U' with
  | nil => rfl
  | cons v vs =>
    exfalso
    have hv := h1 v (.head _)
    cases v with
    | ty a =>
      cases a with
      | named s =>
        have := (h2 s).mp (by simp [namesU, BVar.name?])
        rw [hn] at this; exact List.not_mem_nil this.1
      | _ => simp [BVar.isNamed] at hv
    | row e =>
      cases e with
      | named s =>
        have := (h2 s).mp (by simp [namesU, BVar.name?])
        rw [hn] at this; exact List.not_mem_nil this.1
      | _ => simp [BVar.isNamed] at hv

theorem annScheme_nil (τ : Ty) : annScheme [] τ = mono τ := by
  have h : ∀ l : List BVar, l.filter (fun _ => false) = [] := by
    intro l; induction l <;> simp_all [List.filter_cons]
  simp [annScheme, Scheme.canon, canonVars, dedupL, renumber, apply_id, mono, h]

/-! ## Groups -/

/-- The entries W gives the members of a group, against the derivation's members: the same
    annotations, the types mapped by `S` to the derivation's. -/
def EsRel (S : FSub) : List (Option (BTy × List BVar) × Ty) → AValBind → Prop
  | (ann, τ) :: es, .var _ ann' τ' _ rest =>
    ann = ann' ∧ sb S τ = τ' ∧ (match rest with
      | none => es = []
      | some vb => EsRel S es vb)
  | _, _ => False

/-- The annotations of a chain of members check. -/
def AnnChk (C : Ctx) : AValBind → Prop
  | .var _ ann τ _ rest => checkAnn C ann τ = true ∧ (match rest with
      | none => True
      | some vb => AnnChk C vb)
  | .pat _ _ => True

theorem annChk_of_check {C : Ctx} : ∀ vb : AValBind, checkValBind C vb = true → AnnChk C vb
  | .var _ ann τ e rest, h => by
    simp only [checkValBind, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := h
    unfold AnnChk
    refine ⟨h1, ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annChk_of_check vb (by simpa [checkValBindOpt] using h4)
  | .pat _ _, _ => trivial

def GEPost (n0 : Nat) (st : WSt) (S' : FSub) (vb' : AValBind) (es : List (Option (BTy × List BVar) × Ty))
    (st' : WSt) : Prop :=
  st'.θ = st.θ ∧ st.n ≤ st'.n ∧ SInv n0 st' ∧ (∀ e ∈ es, OkT st'.n e.2 ∧ annU e.1 = []) ∧
    ∃ S1, Found n0 S' st.n st' S1 ∧ EsRel S1 es vb'

theorem EsRel.congr {n : Nat} {S T : FSub} (hT : ∀ a, a.isNew n = false → T a = S a) :
    ∀ (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind), (∀ e ∈ es, OkT n e.2) →
      EsRel S es vb' → EsRel T es vb'
  | (ann, τ) :: es, .var _ ann' τ' _ rest, hok, h => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [sb_agree (hok _ (.head _)) hT, h2], ?_⟩
    cases rest with
    | none => exact h3
    | some vb => exact EsRel.congr hT es vb (fun e he => hok e (.tail _ he)) h3
  | [], _, _, h => by cases h
  | _ :: _, .pat _ _, _, h => by cases h

theorem found_ext1' {n0 : Nat} {S' : FSub} {st : WSt} (hi : SInv n0 st) (hfx : FixesR (rigidFrom n0) S')
    (hab : Absorbs S' (lk st.θ)) (τ' : Ty) : Found n0 S' st.n { st with n := st.n + 1 } (ext1 S' st.n τ') := by
  have hag : ∀ a, a.isNew st.n = false → ext1 S' st.n τ' a = S' a := fun a ha => by
    simp only [ext1]; rw [if_neg]; rintro rfl; simp [TyVar.isNew] at ha
  obtain ⟨h1, h2⟩ := agree_ok hi.le hi.ok hfx hab hag
  refine ⟨h1, h2, hag, fun a ha => ?_⟩
  simp only [ext1] at ha
  split at ha
  · rename_i e; subst e; rfl
  · exact absurd rfl ha

theorem groupEntries_complete {n0 : Nat} {C C2 : Ctx}
    (hU : C2.U = C.U) (hT : ∀ lc, C2.lookupTy lc = C.lookupTy lc) :
    ∀ (vb : BValBind) (st : WSt) (S' : FSub) (vb' : AValBind), SInv n0 st → FixesR (rigidFrom n0) S' →
      Absorbs S' (lk st.θ) → AnnChk C2 vb' → vb'.erase = vb →
      OutP (GEPost n0 st S' vb') (groupEntries C vb st)
  | .pat _ _, _, _, _, _, _, _, _, _ => by simp only [groupEntries]; trivial
  | .var x ann e rest, st, S', vb', hi, hfx, hab, hck, he => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [AValBind.erase, BValBind.var.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      unfold AnnChk at hck
      obtain ⟨hck1, hck2⟩ := hck
      -- the rest of the chain, after the first entry
      have hrest : ∀ (en : Option (BTy × List BVar) × Ty) (st1 : WSt) (S1 : FSub), st1.θ = st.θ →
          st.n ≤ st1.n → SInv n0 st1 → OkT st1.n en.2 → annU en.1 = [] → Found n0 S' st.n st1 S1 →
          en.1 = ann' → sb S1 en.2 = τ' →
          OutP (GEPost n0 st S' (.var x' ann' τ' e' rest'))
            ((do
              let es ← match AValBind.eraseOpt rest' with
                | none => pure []
                | some vb => groupEntries C vb
              pure (en :: es)) st1) := by
        intro en st1 S1 hθ1 hn1 hi1 hok1 hann1 hF1 hen1 hen2
        cases rest' with
        | none =>
          simp only [AValBind.eraseOpt]
          refine outP_bind (outP_pure (P := fun r st' => r = [] ∧ st' = st1) ⟨rfl, rfl⟩) ?_
          rintro _ _ ⟨rfl, rfl⟩
          refine outP_pure ⟨hθ1, hn1, hi1, ?_, S1, hF1, hen1, hen2, rfl⟩
          intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hok1, hann1⟩
        | some vb =>
          simp only [AValBind.eraseOpt]
          refine outP_bind (groupEntries_complete hU hT _ st1 S1 vb hi1 hF1.fix hF1.abs hck2 rfl) ?_
          rintro es st2 ⟨hθ2, hn2, hi2, hes, S2, hF2, hrel⟩
          refine outP_pure ⟨hθ2.trans hθ1, by omega, hi2, ?_, S2, hF1.trans hF2 hn1, hen1, ?_, hrel⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact ⟨hok1.mono hn2, hann1⟩
            · exact hes e he
          · rw [hF2.sb_eq hok1, hen2]
      cases ann' with
      | none =>
        simp only [groupEntries, Option.map_none]
        refine outP_freshV ?_
        refine outP_bind (Q := fun r st' => r = ((none : Option (BTy × List BVar)), Ty.var (.fresh st.n .any)) ∧
          st' = { st with n := st.n + 1 }) (outP_pure ⟨rfl, rfl⟩) ?_
        rintro _ _ ⟨rfl, rfl⟩
        exact hrest _ _ _ rfl (Nat.le_succ _) hi.fresh okT_fresh rfl (found_ext1' hi hfx hab τ') rfl
          (by simp [sb, ext1_self])
      | some p =>
        obtain ⟨ty, U'⟩ := p
        simp only [groupEntries, Option.map_some]
        simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at hck1
        obtain ⟨⟨hnew, hel⟩, -⟩ := hck1
        split
        · rename_i hn
          have hU' := newFor_nil hnew hn
          subst hU'
          have hel' : elabTy (C.plusU []) ty = some τ' := by
            rw [← hel, elabTy_congr (C1 := C.plusU []) (C2 := C2.plusU [])]
            · simp [Ctx.plusU, hU]
            · intro lc; simp only [plusU_nil]; exact (hT lc).symm
          rw [hel']
          simp only
          split
          · rename_i hv
            have hv' : τ'.vars = [] := by simpa using hv
            refine outP_bind (outP_pure (P := fun r st' => r = (some (ty, []), τ') ∧ st' = st) ⟨rfl, rfl⟩) ?_
            rintro _ _ ⟨rfl, rfl⟩
            exact hrest _ _ _ rfl (Nat.le_refl _) hi (OkT_of_vars_nil hv') rfl ⟨hfx, hab, fun _ _ => rfl, fun _ h => absurd rfl h⟩ rfl
              (sb_eq_self_iff.mpr fun a ha => by rw [hv'] at ha; cases ha)
          · simp only [bind, WM.bind, wUnsupported]; trivial
        · simp only [bind, WM.bind, wUnsupported]; trivial
    | pat _ _ => simp [AValBind.erase] at he

/-- The value environment W gives a group, mapped by `S`, is the derivation's. -/
theorem groupVE_rel {S : FSub} : ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRel S es vb' → vb'.erase = vb → (∀ e ∈ es, annU e.1 = []) → sbVE S (groupVE vb es) = vb'.ve
  | .var x ann e rest, (an, τ) :: es, .var x' ann' τ' e' rest', h, he, hann => by
    simp only [AValBind.erase, BValBind.var.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    unfold EsRel at h
    obtain ⟨rfl, h2, h3⟩ := h
    have ha : annU an = [] := hann _ (.head _)
    unfold groupVE AValBind.ve
    rw [sbVE_modify]
    congr 1
    · have : (if an.isSome = true then annScheme (annU an) τ' else mono τ') = mono τ' := by
        split <;> simp [ha, annScheme_nil]
      have h' : (if an.isSome = true then annScheme (annU an) τ else mono τ) = mono τ := by
        split <;> simp [ha, annScheme_nil]
      rw [this, h']; simp [sbVE, sbScheme, h2, mono]
    · cases rest' with
      | none => simp only [AValBind.eraseOpt]; rfl
      | some vb =>
        simp only [AValBind.eraseOpt]
        exact groupVE_rel _ es vb h3 rfl (fun e he => hann e (.tail _ he))
  | .var _ _ _ _, [], _, h, _, _ => by cases ‹AValBind› <;> simp [EsRel] at h
  | .var _ _ _ _, _ :: _, .pat _ _, h, _, _ => by simp [EsRel] at h
  | .pat _ _, _, vb', h, he, _ => by
    cases vb' with
    | var => simp [AValBind.erase] at he
    | pat => cases ‹List _› <;> simp [EsRel] at h

theorem groupVE_mono : ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)), (∀ e ∈ es, annU e.1 = []) →
    ∀ q ∈ groupVE vb es, q.2.1.bound = [] ∧ q.2.2 = .v ∧ ∃ e ∈ es, q.2.1.body = e.2
  | .var x ann e rest, (an, τ) :: es, hann, q, hq => by
    unfold groupVE at hq
    have ha : annU an = [] := hann _ (.head _)
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      have : (if an.isSome = true then annScheme (annU an) τ else mono τ) = mono τ := by
        split <;> simp [ha, annScheme_nil]
      simp only [this]
      exact ⟨by simp [mono], by simp, (an, τ), .head _, by simp [mono]⟩
    · cases rest with
      | none => cases hq
      | some vb =>
        obtain ⟨h1, h2, e', he', h3⟩ := groupVE_mono vb es (fun e he => hann e (.tail _ he)) q hq
        exact ⟨h1, h2, e', .tail _ he', h3⟩
  | .var _ _ _ _, [], _, q, hq => by simp [groupVE] at hq
  | .pat _ _, _, _, q, hq => by simp [groupVE] at hq

/-! ## Monotypes in contexts -/

def NBτ (τ : Ty) : Prop := ∀ v ∈ τ.vars, v.isBnd = false

theorem schRel_mono (s : FSub) (τ : Ty) : SchRel s (mono τ) (mono (sb s τ)) := by
  refine ⟨fun a ha v hv => ?_, fun _ t hg => ?_⟩
  · rw [mono_tyvars] at ha ⊢
    obtain ⟨h1, h2⟩ := mem_tyvars_iff.mp hv
    exact mem_tyvars_iff.mpr ⟨vars_sb_of s τ a v (mem_tyvars_iff.mp ha).1 h1, h2⟩
  · obtain ⟨ts, S, hS, -, hap⟩ := hg
    cases ts with
    | cons _ _ => simp [mono, bindSubst] at hS
    | nil =>
      simp only [mono, bindSubst, Option.some.injEq] at hS; subst hS
      rw [apply_id, Option.some.injEq] at hap
      refine ⟨idS, ?_⟩
      rw [← hap]; simp only [mono]; congr 1

/-- An environment of monotypes and its image. -/
theorem VEMatch_mono {s : FSub} {VE : ValEnv} (h : ∀ q ∈ VE, q.2.1.bound = []) : VEMatch (SchRel s) VE (sbVE s VE) := by
  intro x
  rw [find?_sbVE]
  cases hf : FMap.find? VE x with
  | none => trivial
  | some p =>
    refine ⟨rfl, ?_⟩
    obtain ⟨σ, st⟩ := p
    have hb : σ.bound = [] := h _ (find?_mem hf)
    have : σ = mono σ.body := by cases σ; simp_all [mono]
    simp only
    rw [this]; exact schRel_mono s _

theorem CtxW.plusVE {n : Nat} {C : Ctx} {VE : ValEnv} (hC : CtxW n C) (hVE : ∀ q ∈ VE, SchW n q.2.1) :
    CtxW n (C.plusVE VE) := by
  intro lv σ st hl
  rw [lookupVal_plusVE] at hl
  cases hq : lv.qual with
  | none =>
    cases hf : FMap.find? VE lv.id with
    | some p =>
      simp only [hq, hf, Option.or, Option.some.injEq] at hl; subst hl; exact hVE _ (find?_mem hf)
    | none =>
      simp only [hq, hf, Option.or] at hl
      exact hC ⟨none, lv.id⟩ σ st (by simpa [Ctx.lookupVal, Env.lookupVal] using hl)
  | some m => rw [hq] at hl; exact hC lv σ st hl

/-- The derivation's context of a pattern binding: the pattern's own variables have status v. -/
theorem lkC_plusVE {C : Ctx} {VE : ValEnv} (h : ∀ q ∈ VE, q.2.2 = .v) : LkC (C.plusVE VE) C := by
  intro lv σ' hl
  rw [lookupVal_plusVE] at hl
  cases hq : lv.qual with
  | none =>
    cases hf : FMap.find? VE lv.id with
    | some p =>
      simp only [hq, hf, Option.or, Option.some.injEq] at hl; subst hl
      have := h _ (find?_mem hf); simp at this
    | none =>
      simp only [hq, hf, Option.or] at hl
      simpa [Ctx.lookupVal, Env.lookupVal, hq] using hl
  | some m => rw [hq] at hl; exact hl

theorem lkC_refl (C : Ctx) : LkC C C := fun _ _ h => h

/-! ## The operators -/

theorem otstat_ok : ∀ p ∈ OTstatList, (∀ v ∈ p.2.1.bound, v.isBnd = true) ∧ ∀ v ∈ p.2.1.body.vars, v ∈ p.2.1.bound := by
  decide

theorem otstat_schW {o : Op} {σ : Scheme} {st : IdStatus} (h : OTstat o = some (σ, st)) (n : Nat) : SchW n σ :=
  ⟨(otstat_ok _ (find?_mem h)).1, fun v hv hb => absurd ((otstat_ok _ (find?_mem h)).2 v hv) hb⟩

theorem otstat_rel {o : Op} {σ : Scheme} {st : IdStatus} (h : OTstat o = some (σ, st)) (s : FSub) : SchRel s σ σ :=
  schRel_refl fun a ha hb => absurd ((otstat_ok _ (find?_mem h)).2 _ ha) hb

/-! ## The `let` step (L3 then L4) -/

/-- The free variables of `T (θ C)` are free in `C'`. -/
theorem ctxSb_ftv {n0 n : Nat} {C C' : Ctx} {T : FSub} {θ : Bnd} (hrel : CtxRel (SchRel T) (rigidFrom n0) C C')
    (hC : CtxW n C) (hT : FixesR (rigidFrom n0) T) (habs : Absorbs T (lk θ)) (hg : Good (rigidFrom n0) θ []) :
    ∀ a, BVar.ty a ∈ (ctxSb (lk θ) C).tyvars → ∀ v ∈ (T a).tyvars, v ∈ C'.tyvars := by
  intro a ha v hv
  have hftv := hrel.ftv (fun _ _ h => h.1) hT
  rcases mem_ctx_tyvars.mp ha with ha | ⟨x, p, hf, hp⟩
  · exact hftv a (mem_ctx_tyvars.mpr (.inl (by simpa [restTv, ctxSb] using ha))) v hv
  · simp only [ctxSb] at hf
    rw [find?_sbVE] at hf
    cases hf0 : FMap.find? C.E.VE x with
    | none => rw [hf0] at hf; cases hf
    | some q =>
      rw [hf0] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
      obtain ⟨σ, st⟩ := q
      have hσ : SchW n σ := hC ⟨none, x⟩ σ st (by simpa [Ctx.lookupVal, Env.lookupVal] using hf0)
      simp only [sbScheme, Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
        decide_eq_false_iff_not] at hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
      have hp3 : BVar.ty a ∉ σ.bound := of_decide_eq_false hp3
      obtain ⟨c, hc, hac⟩ := tyvar_sb hp1
      have hcb : BVar.ty c ∉ σ.bound := by
        intro hb
        have hbnd := hσ.1 _ hb
        have : lk θ c = .var c := by
          refine (hg.fixesR c ?_)
          cases c <;> simp_all [BVar.isBnd, rigidFrom]
        rw [this] at hac; simp only [Ty.vars, List.mem_singleton] at hac; rw [hac] at hp3; exact hp3 hb
      obtain ⟨c', e, hc1, -⟩ := hσ.2 _ hc hcb
      injection e with e; subst e
      have hcC : BVar.ty c ∈ C.tyvars := mem_ctx_tyvars.mpr (.inr ⟨x, (σ, st), hf0, by
        simp only [Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact ⟨⟨hc, by cases c <;> simp_all [BVar.isBnd, TyVar.isBndT]⟩, hcb⟩⟩)
      refine hftv c hcC v ?_
      obtain ⟨hv1, hv2⟩ := mem_tyvars_iff.mp hv
      refine mem_tyvars_iff.mpr ⟨?_, hv2⟩
      rw [← habs c]
      exact vars_sb_of T _ a v hac hv1

/-- The context of a `let` body in W, against the derivation's. -/
theorem let_pre {n0 : Nat} {C C' : Ctx} {S' T1 : FSub} {st st1 : WSt} {VE0 VE' : ValEnv}
    (hp : Pre n0 C C' S' st) (hn : st.n ≤ st1.n) (hi1 : SInv n0 st1) (hF : Found n0 S' st.n st1 T1)
    (hVE0 : ∀ q ∈ VE0, q.2.1.bound = [] ∧ OkT st1.n q.2.1.body ∧ NBτ (sb T1 q.2.1.body))
    (hVE' : VE' = sbVE T1 VE0) :
    Pre n0 (C.plusVE (closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0)))
      (C'.plusVE (closGroup C'.tyvars VE')) T1 st1 := by
  have hC1 : CtxW st1.n C := hp.ctxW.mono hn
  have hrel1 := hp.rel.congr hp.ctxW hF.agree
  have hmono : ∀ σ : Scheme, σ.bound = [] → σ = mono σ.body := fun σ h => by cases σ; simp_all [mono]
  refine ⟨hi1, hC1.plusVE fun q hq => ?_, hrel1.plusVE fun x => ?_, hF.fix, hF.abs⟩
  · -- the closures are schemes W can hold
    simp only [closGroup_eq, FMap.mapV, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simp only [sbVE, List.mem_map] at hr
    obtain ⟨p, hp', rfl⟩ := hr
    obtain ⟨hb, hok, -⟩ := hVE0 p hp'
    simp only
    rw [hmono p.2.1 hb]
    exact closE_schW (hi1.ok.okT hok)
  · rw [find?_closGroup, find?_closGroup, find?_sbVE, hVE', find?_sbVE]
    cases hf : FMap.find? VE0 x with
    | none => trivial
    | some p =>
      obtain ⟨hb, hok, hnb⟩ := hVE0 _ (find?_mem hf)
      refine ⟨rfl, ?_⟩
      simp only
      rw [hmono p.1 hb]
      simp only [sbScheme_mono]
      rw [show sb T1 p.1.body = sb T1 (sb (lk st1.θ) p.1.body) from (absorbs_comp hF.abs _).symm]
      refine closE_rel (hi1.ok.okT hok) (fun a ha _ => ctxSb_ftv hrel1 hC1 hF.fix hF.abs hi1.good a ha) ?_
      rw [absorbs_comp hF.abs]; exact hnb

end StandardElm.Stat.Complete
