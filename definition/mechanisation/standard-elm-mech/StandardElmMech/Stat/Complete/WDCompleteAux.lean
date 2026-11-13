/-
  A Standard Definition of Elm? Mechanisation: lemmas for the expression part of the main
  induction L11 with rows (plan step 11, milestone (d), section 8; WCompleteAux.lean for
  `inferExpWD`): groups (the entries before the members are typed, and the value environment
  they give), the operators' schemes, and the `let` step (L3 then L4: the body's context in W,
  closed, against the derivation's, closed; `let_preD`).
-/
import StandardElmMech.Stat.Complete.WDCompletePat
import StandardElmMech.Stat.Complete.WCompleteAux

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BValBind)

/-! ## Groups -/

/-- The entries W gives the members of a group, against the derivation's members: the same
    annotations, the types mapped by `S` to the derivation's. -/
def EsRelD (S : RSub) : List (Option (BTy × List BVar) × Ty) → AValBind → Prop
  | (ann, τ) :: es, .var _ ann' τ' _ rest =>
    ann = ann' ∧ rsb S τ = τ' ∧ (match rest with
      | none => es = []
      | some vb => EsRelD S es vb)
  | _, _ => False


def GEPostD (n0 : Nat) (st : WDSt) (S' : RSub) (vb' : AValBind) (es : List (Option (BTy × List BVar) × Ty))
    (st' : WDSt) : Prop :=
  st'.θ = st.θ ∧ st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ e ∈ es, OkTD st'.n e.2 ∧ annU e.1 = []) ∧
    ∃ S1, FoundD n0 S' st.n st' S1 ∧ EsRelD S1 es vb'

theorem EsRelD.congr {n : Nat} {S T : RSub} (hT : ∀ v, newB n v = false → T.img v = S.img v) :
    ∀ (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind), (∀ e ∈ es, OkTD n e.2) →
      EsRelD S es vb' → EsRelD T es vb'
  | (ann, τ) :: es, .var _ ann' τ' _ rest, hok, h => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [rsb_agreeD (hok _ (.head _)).old hT, h2], ?_⟩
    cases rest with
    | none => exact h3
    | some vb => exact EsRelD.congr hT es vb (fun e he => hok e (.tail _ he)) h3
  | [], _, _, h => by cases h
  | _ :: _, .pat _ _, _, h => by cases h

theorem groupEntries_completeD {n0 : Nat} {C C2 : Ctx}
    (hU : C2.U = C.U) (hT : ∀ lc, C2.lookupTy lc = C.lookupTy lc) :
    ∀ (vb : BValBind) (st : WDSt) (S' : RSub) (vb' : AValBind), SInvD n0 st → FixR (rigidFromD n0) S' →
      AbsR S' st.θ → AnnChk C2 vb' → vb'.erase = vb →
      OutPD (GEPostD n0 st S' vb') (groupEntriesD C vb st)
  | .pat _ _, _, _, _, _, _, _, _, _ => by simp only [groupEntriesD]; trivial
  | .var x ann e rest, st, S', vb', hi, hfx, hab, hck, he => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [AValBind.erase, BValBind.var.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      unfold AnnChk at hck
      obtain ⟨hck1, hck2⟩ := hck
      -- the rest of the chain, after the first entry
      have hrest : ∀ (en : Option (BTy × List BVar) × Ty) (st1 : WDSt) (S1 : RSub), st1.θ = st.θ →
          st.n ≤ st1.n → SInvD n0 st1 → OkTD st1.n en.2 → annU en.1 = [] → FoundD n0 S' st.n st1 S1 →
          en.1 = ann' → rsb S1 en.2 = τ' →
          OutPD (GEPostD n0 st S' (.var x' ann' τ' e' rest'))
            ((do
              let es ← match AValBind.eraseOpt rest' with
                | none => pure []
                | some vb => groupEntriesD C vb
              pure (en :: es)) st1) := by
        intro en st1 S1 hθ1 hn1 hi1 hok1 hann1 hF1 hen1 hen2
        cases rest' with
        | none =>
          simp only [AValBind.eraseOpt]
          refine outP_bindD (outP_pureD (P := fun r st' => r = [] ∧ st' = st1) ⟨rfl, rfl⟩) ?_
          rintro _ _ ⟨rfl, rfl⟩
          refine outP_pureD ⟨hθ1, hn1, hi1, ?_, S1, hF1, hen1, hen2, rfl⟩
          intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hok1, hann1⟩
        | some vb =>
          simp only [AValBind.eraseOpt]
          refine outP_bindD (groupEntries_completeD hU hT _ st1 S1 vb hi1 hF1.fix hF1.abs hck2 rfl) ?_
          rintro es st2 ⟨hθ2, hn2, hi2, hes, S2, hF2, hrel⟩
          refine outP_pureD ⟨hθ2.trans hθ1, by omega, hi2, ?_, S2, hF1.trans hF2 hn1, hen1, ?_, hrel⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact ⟨hok1.mono hn2, hann1⟩
            · exact hes e he
          · rw [hF2.sb_eq hok1, hen2]
      cases ann' with
      | none =>
        simp only [groupEntriesD, Option.map_none]
        refine outP_freshVD ?_
        refine outP_bindD (Q := fun r st' => r = ((none : Option (BTy × List BVar)), Ty.var (.fresh st.n .any)) ∧
          st' = { st with n := st.n + 1 }) (outP_pureD ⟨rfl, rfl⟩) ?_
        rintro _ _ ⟨rfl, rfl⟩
        exact hrest _ _ _ rfl (Nat.le_succ _) hi.fresh okT_freshD rfl (found_ext1CD' hi hfx hab (Adm.any τ')) rfl
          (by simp [rsb, ext1CD])
      | some p =>
        obtain ⟨ty, U'⟩ := p
        simp only [groupEntriesD, Option.map_some]
        simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at hck1
        obtain ⟨⟨hnew, hel⟩, -⟩ := hck1
        split
        · rename_i hn
          have hU' := newFor_nil hnew (Bool.and_eq_true _ _ ▸ hn).1
          subst hU'
          have hel' : elabTy (C.plusU []) ty = some τ' := by
            rw [← hel, elabTy_congrW (C1 := C.plusU []) (C2 := C2.plusU [])]
            · simp [Ctx.plusU, hU]
            · intro lc; simp only [plusU_nil]; exact (hT lc).symm
          rw [hel']
          simp only
          split
          · rename_i hv
            have hv' : τ'.vars = [] := by simpa using hv
            refine outP_bindD (outP_pureD (P := fun r st' => r = (some (ty, []), τ') ∧ st' = st) ⟨rfl, rfl⟩) ?_
            rintro _ _ ⟨rfl, rfl⟩
            exact hrest _ _ _ rfl (Nat.le_refl _) hi (OkT_of_vars_nilD hv') rfl ⟨hfx, hab, fun _ _ => rfl, fun _ h => absurd rfl h⟩ rfl
              (rsb_eq_self fun w hw => by rw [hv'] at hw; cases hw)
          · simp only [bind, WDM.bind, wdUnsupported]; trivial
        · simp only [bind, WDM.bind, wdUnsupported]; trivial
    | pat _ _ => simp [AValBind.erase] at he

/-- The value environment W gives a group, mapped by `S`, is the derivation's. -/
theorem groupVE_relD {S : RSub} : ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRelD S es vb' → vb'.erase = vb → (∀ e ∈ es, annU e.1 = []) → rsbVE S (groupVE vb es) = vb'.ve
  | .var x ann e rest, (an, τ) :: es, .var x' ann' τ' e' rest', h, he, hann => by
    simp only [AValBind.erase, BValBind.var.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    unfold EsRelD at h
    obtain ⟨rfl, h2, h3⟩ := h
    have ha : annU an = [] := hann _ (.head _)
    unfold groupVE AValBind.ve
    rw [rsbVE_modifyD]
    congr 1
    · have : (if an.isSome = true then annScheme (annU an) τ' else mono τ') = mono τ' := by
        split <;> simp [ha, annScheme_nil]
      have h' : (if an.isSome = true then annScheme (annU an) τ else mono τ) = mono τ := by
        split <;> simp [ha, annScheme_nil]
      rw [this, h']; simp [rsbVE, rsbScheme, h2, mono]
    · cases rest' with
      | none => simp only [AValBind.eraseOpt]; rfl
      | some vb =>
        simp only [AValBind.eraseOpt]
        exact groupVE_relD _ es vb h3 rfl (fun e he => hann e (.tail _ he))
  | .var _ _ _ _, [], _, h, _, _ => by cases ‹AValBind› <;> simp [EsRelD] at h
  | .var _ _ _ _, _ :: _, .pat _ _, h, _, _ => by simp [EsRelD] at h
  | .pat _ _, _, vb', h, he, _ => by
    cases vb' with
    | var => simp [AValBind.erase] at he
    | pat => cases ‹List _› <;> simp [EsRelD] at h

theorem groupVE_monoD : ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)), (∀ e ∈ es, annU e.1 = []) →
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
        obtain ⟨h1, h2, e', he', h3⟩ := groupVE_monoD vb es (fun e he => hann e (.tail _ he)) q hq
        exact ⟨h1, h2, e', .tail _ he', h3⟩
  | .var _ _ _ _, [], _, q, hq => by simp [groupVE] at hq
  | .pat _ _, _, _, q, hq => by simp [groupVE] at hq

/-! ## Monotypes in contexts -/


theorem schRel_monoD (s : RSub) (τ : Ty) : SchRelD s (mono τ) (mono (rsb s τ)) := by
  refine ⟨fun w hw v hv => ?_, fun t hg => ?_⟩
  · rw [mono_tyvars] at hw ⊢
    obtain ⟨h1, h2⟩ := mem_tyvars_iff.mp hv
    exact mem_tyvars_iff.mpr ⟨(mem_vars_rsb s τ v).mpr ⟨w, (mem_tyvars_iff.mp hw).1, h1⟩, h2⟩
  · obtain ⟨g, -, hout, rfl⟩ := gen_rsb hg
    refine ⟨rid, fun _ h => by simp [mono] at h, ?_⟩
    rw [rsb_eq_self fun w _ => hout w (by simp [mono])]
    simp only [mono_body]
    exact rsb_congr _ fun w _ => by rw [extS_img]; simp [mono]

/-- An environment of monotypes and its image. -/
theorem VEMatch_monoD {s : RSub} {VE : ValEnv} (h : ∀ q ∈ VE, q.2.1.bound = []) : VEMatch (SchRelD s) VE (rsbVE s VE) := by
  intro x
  rw [find?_rsbVE]
  cases hf : FMap.find? VE x with
  | none => trivial
  | some p =>
    refine ⟨rfl, ?_⟩
    obtain ⟨σ, st⟩ := p
    have hb : σ.bound = [] := h _ (find?_mem hf)
    have : σ = mono σ.body := by cases σ; simp_all [mono]
    simp only
    rw [this]; exact schRel_monoD s _

theorem CtxWD.plusVE {n : Nat} {C : Ctx} {VE : ValEnv} (hC : CtxWD n C) (hVE : ∀ q ∈ VE, SchWD n q.2.1) :
    CtxWD n (C.plusVE VE) := by
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

/-! ## The operators -/

theorem otstat_schWD {o : Op} {σ : Scheme} {st : IdStatus} (h : OTstat o = some (σ, st)) (n : Nat) : SchWD n σ :=
  ⟨(otstat_ok _ (find?_mem h)).1, fun v hv hb => absurd ((otstat_ok _ (find?_mem h)).2 v hv) hb⟩

theorem otstat_relD {o : Op} {σ : Scheme} {st : IdStatus} (h : OTstat o = some (σ, st)) (s : RSub) : SchRelD s σ σ :=
  schRel_reflD fun w hw hb => absurd ((otstat_ok _ (find?_mem h)).2 _ hw) hb

/-! ## The `let` step (L3 then L4) -/

/-- The accumulated substitution moves no rigid variable. -/
theorem goodR_fix {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X) {v : BVar}
    (hv : R v = true) : (toRS θ).img v = vty v := by
  rw [img_toRS g.rrec]
  cases hf : FMap.find? θ v with
  | none => rfl
  | some σ => have := g.keys _ (rfind?_mem hf); simp only at this; rw [hv] at this; cases this

/-- The free variables of `T (θ C)` are free in `C'`. -/
theorem ctxSb_ftvD {n0 n : Nat} {C C' : Ctx} {T : RSub} {θ : RBnd} (hrel : CtxRelD (SchRelD T) (rigidFromD n0) C C')
    (hC : CtxWD n C) (hT : FixR (rigidFromD n0) T) (habs : AbsR T θ) {m : Nat}
    (hg : GoodR (rigidFromD n0) m θ [] []) :
    ∀ w ∈ (ctxRsb (toRS θ) C).tyvars, ∀ v ∈ (T.img w).tyvars, v ∈ C'.tyvars := by
  intro w hw v hv
  have hftv := hrel.ftv (fun _ _ h => h.1) hT
  rcases mem_ctx_tyvars.mp hw with hw | ⟨x, p, hf, hp⟩
  · exact hftv w (mem_ctx_tyvars.mpr (.inl (by simpa [restTv, ctxRsb] using hw))) v hv
  · simp only [ctxRsb] at hf
    rw [find?_rsbVE] at hf
    cases hf0 : FMap.find? C.E.VE x with
    | none => rw [hf0] at hf; cases hf
    | some q =>
      rw [hf0] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
      obtain ⟨σ, st⟩ := q
      have hσ : SchWD n σ := hC ⟨none, x⟩ σ st (by simpa [Ctx.lookupVal, Env.lookupVal] using hf0)
      simp only [rsbScheme, Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
        decide_eq_false_iff_not] at hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
      have hp3 : w ∉ σ.bound := of_decide_eq_false hp3
      obtain ⟨c, hc, hwc⟩ := (mem_vars_rsb _ _ w).mp hp1
      have hcb : c ∉ σ.bound := by
        intro hb
        rw [goodR_fix hg (rigidFromD_bnd n0 (hσ.1 c hb)), vars_vty, List.mem_singleton] at hwc
        rw [hwc] at hp3; exact hp3 hb
      have hcC : c ∈ C.tyvars := mem_ctx_tyvars.mpr (.inr ⟨x, (σ, st), hf0, by
        simp only [Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact ⟨⟨hc, (hσ.2 c hc hcb).1⟩, hcb⟩⟩)
      refine hftv c hcC v ?_
      obtain ⟨hv1, hv2⟩ := mem_tyvars_iff.mp hv
      refine mem_tyvars_iff.mpr ⟨?_, hv2⟩
      rw [← habs c]
      exact (mem_vars_rsb T _ v).mpr ⟨w, hwc, hv1⟩

/-- The context of a `let` body in W, against the derivation's. -/
theorem let_preD {n0 : Nat} {C C' : Ctx} {S' T1 : RSub} {st st1 : WDSt} {VE0 VE' : ValEnv}
    (hp : PreD n0 C C' S' st) (hn : st.n ≤ st1.n) (hi1 : SInvD n0 st1) (hF : FoundD n0 S' st.n st1 T1)
    (hVE0 : ∀ q ∈ VE0, q.2.1.bound = [] ∧ OkTD st1.n q.2.1.body ∧ NBτ (rsb T1 q.2.1.body))
    (hVE' : VE' = rsbVE T1 VE0) :
    PreD n0 (C.plusVE (closGroup (ctxRsb (toRS st1.θ) C).tyvars (rsbVE (toRS st1.θ) VE0)))
      (C'.plusVE (closGroup C'.tyvars VE')) T1 st1 := by
  have hC1 : CtxWD st1.n C := hp.ctxW.mono hn
  have hrel1 := hp.rel.congr hp.ctxW hF.agree
  have hmono : ∀ σ : Scheme, σ.bound = [] → σ = mono σ.body := fun σ h => by cases σ; simp_all [mono]
  refine ⟨hi1, hC1.plusVE fun q hq => ?_, hrel1.plusVE fun x => ?_, hF.fix, hF.abs, hF.resp hp.resp⟩
  · -- the closures are schemes W can hold
    simp only [closGroup_eq, FMap.mapV, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simp only [rsbVE, List.mem_map] at hr
    obtain ⟨p, hp', rfl⟩ := hr
    obtain ⟨hb, hok, hnb⟩ := hVE0 p hp'
    simp only
    rw [hmono p.2.1 hb]
    exact closE_schWD (okT_theta hi1 hok hF.fix hF.abs hnb)
  · rw [find?_closGroup, find?_closGroup, find?_rsbVE, hVE', find?_rsbVE]
    cases hf : FMap.find? VE0 x with
    | none => trivial
    | some p =>
      obtain ⟨hb, hok, hnb⟩ := hVE0 _ (find?_mem hf)
      refine ⟨rfl, ?_⟩
      simp only
      rw [hmono p.1 hb]
      simp only [rsbScheme_monoD]
      rw [show rsb T1 p.1.body = rsb T1 (rsb (toRS st1.θ) p.1.body) from (absorbs_compD hF.abs _).symm]
      refine closE_relD (okT_theta hi1 hok hF.fix hF.abs hnb) (hF.resp hp.resp)
        (fun w hw _ => ctxSb_ftvD hrel1 hC1 hF.fix hF.abs hi1.good w hw) ?_
      rw [absorbs_compD hF.abs]; exact hnb

end StandardElm.Stat.Complete
