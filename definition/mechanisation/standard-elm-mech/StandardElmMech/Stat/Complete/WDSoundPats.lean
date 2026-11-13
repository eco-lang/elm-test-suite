/-
  A Standard Definition of Elm? Mechanisation: L10 for patterns with records (plan step 11,
  milestone (d)): the induction over W's patterns (`wdAtPat_sound` and the others).
-/
import StandardElmMech.Stat.Complete.WDSoundPat

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExp BMatch BMRule BDec BValBind)

namespace WDS

theorem cov_listTyD {τ : Ty} {l : List Ty} (h : ∀ v ∈ τ.vars, ∃ τ' ∈ l, v ∈ τ'.vars) : Cov [listTy τ] l := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  simp only [listTy, Ty.vars, Ty.listVars, List.append_nil] at hv
  exact h v hv

theorem tysAtPats_memD {a : AAtPat} {l : List AAtPat} {τ : Ty} (ha : a ∈ l) (hτ : τ ∈ tysAtPat a) :
    τ ∈ tysAtPats l := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [tysAtPats, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact .inl hτ
    · exact .inr (ih ha)

theorem cnL_atpats {U : RSub} (hU : U.r (.bnd 0) = ([], some (.bnd 0))) {l : List AAtPat} (h : CnL U (tysAtPats l)) :
    ∀ x ∈ AAtPat.tyList l, cnB (rsb U x) = true := by
  intro x hx
  rw [tyList_eq_map] at hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact cnU_atpat hU (h.sub fun τ hτ => tysAtPats_memD ha hτ)

/-- The check of a pattern, under `s`, given a canonical `U` absorbing `s`. -/
abbrev PCk (n0 : Nat) (L : LongId → Option Scheme) (s : RSub) (l : List Ty) (W : RSub → Prop) (c : Bool) : Prop :=
  ∀ U, GoodU n0 U s → CnL U l → W U → c = true

mutual
theorem wdAtPat_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (p : BAtPat) (C : Ctx) (st : WDSt) (r : Ty × AAtPat) (st' : WDSt),
    SPre n0 L C st → wdAtPat fuel (rigidFromD n0) C p st = .ok r st' →
    r.1 = r.2.ty ∧ PostK n0 C st st' (tysAtPat r.2)
      (fun s => PCk n0 L s (tysAtPat r.2) (fun U => CWAtPat L U r.2) (checkAtPat (ctxRsb s C) (rsbAtPat s r.2))) []
  | .wild, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wdbind_ok h
    obtain ⟨rfl, rfl⟩ := freshVD_ok h1
    obtain ⟨rfl, rfl⟩ := pure_okD h2
    exact ⟨rfl, (PostK.start hp).fresh.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ)
      fun _ _ _ _ _ _ _ => rfl⟩
  | .var x, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wdbind_ok h
    obtain ⟨rfl, rfl⟩ := freshVD_ok h1
    obtain ⟨rfl, rfl⟩ := pure_okD h2
    exact ⟨rfl, (PostK.start hp).fresh.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ)
      fun _ _ _ _ _ _ _ => rfl⟩
  | .scon sc, C, st, r, st', hp, h => by
    cases sc with
    | int k =>
      simp only [wdAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨rfl, PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtPat _ (.scon _ (rsb s tIntTy)) = true; rw [rsb_closedD rfl]; rfl⟩
    | char c =>
      simp only [wdAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨rfl, PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtPat _ (.scon _ (rsb s tCharTy)) = true; rw [rsb_closedD rfl]; rfl⟩
    | str c =>
      simp only [wdAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨rfl, PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtPat _ (.scon _ (rsb s tStringTy)) = true; rw [rsb_closedD rfl]; rfl⟩
    | float m e => simp only [wdAtPat] at h; cases h
  | .con lc, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h
      cases x with
      | v => cases h
      | c =>
      dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wdbind_ok h
      have hpi := post_instD hp (hp.ctxW _ _ _ hl) (lookup_factsD hp hl).1 h1
      dsimp only at h2
      split at h2
      · obtain ⟨rfl, rfl⟩ := pure_okD h2
        refine ⟨rfl, hpi.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ) fun s hs hg U hU hcn _ => ?_⟩
        have hc := hU.cn (hcn _ (List.mem_singleton_self _))
        simp only [checkAtPat, rsbAtPat, (lookup_factsD hp hl).2 s hs, hg hc, Bool.true_and]
        simp [rsb, isConTy]
      · cases h2
      · cases h2
  | .unit, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨rfl, (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysAtPat] at hτ) fun _ _ _ _ _ _ _ => rfl⟩
  | .tuple p1 p2 p3, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨⟨τ2, a2⟩, st2, h2, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨⟨τ3, a3⟩, st3, h3, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p1 C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wdPat_sound fuel n0 hL p2 C st1 _ st2 (hp.later P1.seg) h2
    have P12 := PostK.seqSame hp P1 P2
    obtain ⟨e3, P3⟩ := wdPatOpt_sound fuel n0 hL p3 C st2 _ st3 (hp.later P12.seg) h3
    have P123 := PostK.seqSame hp P12 P3
    obtain ⟨rfl, rfl⟩ := pure_okD h
    refine ⟨by simp only at e1 e2 e3; simp [AAtPat.ty, e1, e2, e3], ?_⟩
    refine P123.weaken (cov_refl _) fun s _ ⟨⟨c1, c2⟩, c3⟩ U hU hcn ⟨w1, w2, w3⟩ => ?_
    simp only [tysAtPat] at hcn
    simp only [checkAtPat, rsbAtPat, Bool.and_eq_true]
    exact ⟨⟨c1 U hU (hcn.sub fun τ hτ => by simp [hτ]) w1, c2 U hU (hcn.sub fun τ hτ => by simp [hτ]) w2⟩,
      c3 U hU (hcn.sub fun τ hτ => by simp [hτ]) w3⟩
  | .nil, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wdbind_ok h
    obtain ⟨rfl, rfl⟩ := freshVD_ok h1
    obtain ⟨rfl, rfl⟩ := pure_okD h2
    refine ⟨rfl, (PostK.start hp).fresh.weaken (cov_listTyD fun v hv => ⟨_, by simp, hv⟩) fun s _ _ _ _ _ _ => ?_⟩
    simp [checkAtPat, rsbAtPat, isListTy, listTy, rsb, rsbList]
  | .record row, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨ar, st1, h1, h⟩ := wdbind_ok h
    obtain ⟨e, st2, h2, h⟩ := wdbind_ok h
    obtain ⟨rfl, rfl⟩ := freshRowD_ok h2
    obtain ⟨rfl, rfl⟩ := pure_okD h
    have P1 := (wdPatRowOpt_sound fuel n0 row st ar st1 hp h1).freshRow
    refine ⟨rfl, P1.weaken ?_ fun s _ _ U hU hcn _ => check_record (hU.cn (hcn _ (by simp [tysAtPat])))⟩
    intro x hx v hv
    simp only [tysAtPat, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [vars_record] at hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨p, hp', hvp⟩ := mem_rowVarsR.mp hv
        exact ⟨p.2, List.mem_append_left _ (mem_rowOpt_tys hp'), hvp⟩
      · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        simp only [tailVars, List.mem_singleton] at hv; subst hv; simp [Ty.vars, Ty.rowVars]
    · exact ⟨x, List.mem_append_left _ hx, hv⟩
  | .paren p, C, st, r, st', hp, h => by
    simp only [wdAtPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkAtPat, rsbAtPat] using c U hU hcn hw⟩
theorem wdPat_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (p : BPat) (C : Ctx) (st : WDSt) (r : Ty × APat) (st' : WDSt),
    SPre n0 L C st → wdPat fuel (rigidFromD n0) C p st = .ok r st' →
    r.1 = r.2.ty ∧ PostK n0 C st st' (tysPat r.2)
      (fun s => PCk n0 L s (tysPat r.2) (fun U => CWPat L U r.2) (checkPat (ctxRsb s C) (rsbPat s r.2))) []
  | .atpat a, C, st, r, st', hp, h => by
    simp only [wdPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wdAtPat_sound fuel n0 hL a C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkPat, rsbPat] using c U hU hcn hw⟩
  | .con lc args, C, st, r, st', hp, h => by
    simp only [wdPat] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h
      cases x with
      | v => cases h
      | c =>
      dsimp only at h
      obtain ⟨⟨ts, τb⟩, st1, h1, h⟩ := wdbind_ok h
      dsimp only at h
      have hpi := post_instD hp (hp.ctxW _ _ _ hl) (lookup_factsD hp hl).1 h1
      cases hpeel : peel args.length τb with
      | none => rw [hpeel] at h; dsimp only at h; split at h <;> cases h
      | some pr =>
      obtain ⟨τs, r0⟩ := pr
      rw [hpeel] at h
      cases r0 with
      | var _ => cases h
      | fn _ _ => cases h
      | record _ _ => cases h
      | con us t =>
        dsimp only at h
        have hτb : τb = arrows τs (.con us t) := by
          have := (peel_rsbD (s := rid) _ _ _ _ hpeel).2
          rwa [rsb_rid, rsbList_rid, rsb_rid] at this
        obtain ⟨ps, st2, h2, h⟩ := wdbind_ok h
        obtain ⟨_, st3, h3, h⟩ := wdbind_ok h
        obtain ⟨e2, P2⟩ := wdAtPats_sound fuel n0 hL args C st1 ps st2 (hp.later hpi.seg) h2
        have P12 := PostK.seqSame hp hpi P2
        have hmap : ps.map (·.1) = AAtPat.tyList (ps.map (·.2)) := by
          rw [tyList_eq_map, List.map_map]
          exact List.map_congr_left fun p hp' => e2 p hp'
        have hcovA : Cov (ps.map (·.1)) (tysAtPats (ps.map (·.2))) := by
          intro x hx v hv
          rw [hmap, tyList_eq_map] at hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars a v hv
          exact ⟨τ', tysAtPats_memD ha h1', h2'⟩
        have hc : Cov (ps.map (·.1) ++ τs) ([τb] ++ tysAtPats (ps.map (·.2))) := by
          intro x hx v hv
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨τ', h1', h2'⟩ := hcovA x hx v hv
            exact ⟨τ', List.mem_append_right _ h1', h2'⟩
          · exact ⟨τb, by simp, by rw [hτb]; exact arrows_vars_left hx hv⟩
        have P3 := P12.uargsD _ _ _ _ _ hc h3
        have hlen := unifyArgsD_length h3
        obtain ⟨rfl, rfl⟩ := pure_okD h
        obtain ⟨hts, hτ, hθ1, hn1⟩ := instantiateD_ok h1
        have P2' := P2.weaken (tys' := ps.map (·.1)) hcovA fun _ _ c => c
        refine ⟨rfl, P3.weaken ?_ fun s hs ⟨⟨hg, hcs⟩, hab2, he⟩ U hU hcn hcw => ?_⟩
        · intro x hx v hv
          simp only [tysPat, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨τb, by simp, by rw [hτb]; exact arrows_vars_right hv⟩
          · exact ⟨x, List.mem_append_right _ hx, hv⟩
        have hU0 := fix_bnd0D hU.1
        simp only [tysPat] at hcn
        have hcnA : CnL U (tysAtPats (ps.map (·.2))) := hcn.sub fun τ hτ => List.mem_cons_of_mem _ hτ
        have hcnArgs : CnL U (ps.map (·.1)) := fun x hx => cnL_atpats hU0 hcnA x (by rw [← hmap]; exact hx)
        have hUP : UPrem n0 st2 (ps.map (·.1)) τs := by
          refine con_uprem hp.inv hθ1 hn1 (by rw [← hτ, hτb]) (by rw [hlen]) P2.seg (fun c hc => hp.old hc)
            P2'.reach (hp.ctxW _ _ _ hl) (hL lc σ (hp.cons lc σ hl)) hU.1 hU.2.1 (absS_trans hU.2.2 hab2)
            hcnArgs ?_
          obtain ⟨ts', hts'⟩ := hcw.1 σ (hp.cons lc σ hl)
          exact ⟨ts', by rw [hmap]; exact hts'⟩
        have heq := he hUP
        have hcb : cnB (rsb s τb) = true := by
          rw [hτb, arrows_sbD, ← heq]
          refine cnB_arrows (hU.cn (hcn _ (List.mem_cons_self ..))) fun x hx => ?_
          rw [rsbList_eq] at hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact hU.cn (hcnArgs y hy)
        simp only [checkPat, rsbPat, (lookup_factsD hp hl).2 s hs, Bool.and_eq_true]
        refine ⟨⟨?_, by simp [rsb, isConTy]⟩, hcs U hU hcnA hcw.2⟩
        rw [rsbAtPats_tyListD, ← hmap, heq, ← arrows_sbD, ← hτb]
        exact hg hcb
  | .cons p1 p2, C, st, r, st', hp, h => by
    simp only [wdPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h
    dsimp only at k1
    obtain ⟨⟨τ2, a2⟩, st2, h2, k2⟩ := wdbind_ok k1
    dsimp only at k2
    obtain ⟨_, st3, h3, k3⟩ := wdbind_ok k2
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p1 C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wdPat_sound fuel n0 hL p2 C st1 _ st2 (hp.later P1.seg) h2
    simp only at e1 e2; subst e1; subst e2
    have P12 := PostK.seqSame hp P1 P2
    have hc : Cov [a2.ty, listTy a1.ty] (tysPat a1 ++ tysPat a2) := by
      intro x hx v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · obtain ⟨τ', h1', h2'⟩ := pat_ty_vars a2 v hv; exact ⟨τ', List.mem_append_right _ h1', h2'⟩
      · simp only [listTy, Ty.vars, Ty.listVars, List.append_nil] at hv
        obtain ⟨τ', h1', h2'⟩ := pat_ty_vars a1 v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩
    have P3 := P12.unify hc h3
    obtain ⟨rfl, rfl⟩ := pure_okD k3
    refine ⟨rfl, P3.weaken (cov_refl _) fun s _ ⟨⟨c1, c2⟩, hab2, he⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩
    simp only [tysPat] at hcn
    have hcn1 : CnL U (tysPat a1) := hcn.sub fun τ hτ => List.mem_append_left _ hτ
    have hcn2 : CnL U (tysPat a2) := hcn.sub fun τ hτ => List.mem_append_right _ hτ
    have hab := absS_trans hU.2.2 hab2
    have eq := he (cnB_of_rsb (s := U) (by rw [absS_rsb hab]; exact cnU_pat hcn2))
      (cnB_of_rsb (s := U) (by rw [absS_rsb hab]; exact cnB_list (cnU_pat hcn1)))
    simp only [checkPat, rsbPat, c1 U hU hcn1 w1, c2 U hU hcn2 w2, Bool.true_and, decide_eq_true_eq, rsbPat_tyD, eq,
      listTy_sbD]
  | .as p x, C, st, r, st', hp, h => by
    simp only [wdPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkPat, rsbPat] using c U hU hcn hw⟩
theorem wdPatOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (p : Option BPat) (C : Ctx) (st : WDSt) (r : Option Ty × Option APat) (st' : WDSt),
    SPre n0 L C st → wdPatOpt fuel (rigidFromD n0) C p st = .ok r st' →
    r.1 = APat.tyOpt r.2 ∧ PostK n0 C st st' (tysPatOpt r.2)
      (fun s => PCk n0 L s (tysPatOpt r.2) (fun U => CWPatOpt L U r.2) (checkPatOpt (ctxRsb s C) (rsbPatOpt s r.2))) []
  | none, C, st, r, st', hp, h => by
    simp only [wdPatOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨rfl, (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysPatOpt] at hτ) fun _ _ _ _ _ _ _ => rfl⟩
  | some p, C, st, r, st', hp, h => by
    simp only [wdPatOpt] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wdbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨by simp only at e1; simp [APat.tyOpt, e1], P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkPatOpt, rsbPatOpt] using c U hU hcn hw⟩
theorem wdAtPats_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (l : List BAtPat) (C : Ctx) (st : WDSt) (r : List (Ty × AAtPat)) (st' : WDSt),
    SPre n0 L C st → wdAtPats fuel (rigidFromD n0) C l st = .ok r st' →
    (∀ p ∈ r, p.1 = p.2.ty) ∧ PostK n0 C st st' (tysAtPats (r.map (·.2)))
      (fun s => PCk n0 L s (tysAtPats (r.map (·.2))) (fun U => CWAtPats L U (r.map (·.2)))
        (checkAtPatList (ctxRsb s C) (rsbAtPats s (r.map (·.2))))) []
  | [], C, st, r, st', hp, h => by
    simp only [wdAtPats] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨(fun _ h => nomatch h), (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysAtPats] at hτ)
      fun _ _ _ _ _ _ _ => rfl⟩
  | a :: as, C, st, r, st', hp, h => by
    simp only [wdAtPats] at h
    obtain ⟨r1, st1, h1, h⟩ := wdbind_ok h
    obtain ⟨rs, st2, h2, h⟩ := wdbind_ok h
    obtain ⟨e1, P1⟩ := wdAtPat_sound fuel n0 hL a C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wdAtPats_sound fuel n0 hL as C st1 _ st2 (hp.later P1.seg) h2
    have P12 := PostK.seqSame hp P1 P2
    obtain ⟨rfl, rfl⟩ := pure_okD h
    refine ⟨fun p hp' => ?_, P12.weaken (cov_refl _) fun s _ ⟨c1, c2⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩
    · rcases List.mem_cons.mp hp' with rfl | hp'
      · exact e1
      · exact e2 p hp'
    · simp only [List.map_cons, tysAtPats] at hcn
      simp only [List.map_cons, checkAtPatList, rsbAtPats, Bool.and_eq_true]
      exact ⟨c1 U hU (hcn.sub fun τ hτ => List.mem_append_left _ hτ) w1,
        c2 U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) w2⟩
end

end WDS

end StandardElm.Stat.Complete
