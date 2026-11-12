/-
  A Standard Definition of Elm? Mechanisation: L10 of plan step 11 (milestone (b), section 8),
  the induction over W for expressions, matches, declarations and groups: what a call returns is
  accepted by the checker under every later substitution that fixes the rigid variables, absorbs
  the call's final substitution and respects the closures taken inside (`PostK`).

  The `let` case is the one that needs the constraints: the closure W took under the substitution
  of that moment commutes with the later one (`closGroup_sb`) because the later substitution
  respects the constraint the closure records (`kseg_clos`); every later call reaches only
  variables outside the generalised ones (`AvoidK`), so the constraint is kept.
  Groups and `case` alternatives accumulate into the conclusion of the enclosing call
  (`wMembers_sound`, `wMatchOpt_sound`), since their types are typed against the entries and the
  first alternative.
-/
import StandardElmMech.Stat.Complete.WSoundAux

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

theorem otstat_sbScheme {o : Op} {σ : Scheme} {x : IdStatus} (h : OTstat o = some (σ, x)) {n0 : Nat} {s : FSub}
    (hs : SOk n0 s) : sbScheme s σ = σ := by
  obtain ⟨hb, hv⟩ := otstat_ok _ (find?_mem h)
  obtain ⟨bd, body⟩ := σ
  simp only [sbScheme, Scheme.mk.injEq, true_and]
  refine sb_eq_self_iff.mpr fun a ha => ?_
  have := hb _ (hv _ ha)
  cases a with
  | bnd i c => exact hs.bnd i c
  | _ => simp [BVar.isBnd] at this

/-- An integer constant at a number type: its scheme's instance. -/
theorem genAt_int {k : Nat} {τ : Ty} (h : Adm .num τ) : genAt (typeOf (.int k)) (litInst (.int k) τ) τ = true := by
  have hr : adm .num τ = true := (adm_iff _ _).mpr h
  simp [genAt, typeOf, litInst, bindSubst, Subst.respectsB, Subst.apply, FMap.find?, TyVar.cls, hr]

theorem getθ_ok {st st' : WSt} {θ : Bnd} (h : getθ st = .ok θ st') : θ = st.θ ∧ st' = st := by
  change WOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

/-- The checker's context of the root is the root context: W's substitution moves no variable of
    its bindings (`old_of_root_ve`). -/
theorem ctxSb_root {C0 : Ctx} {s : FSub} (hs : FixesR (rigidFrom (freshAbove C0)) s) : ctxSb s C0 = C0 := by
  obtain ⟨T, U, ⟨QE, TE, VE⟩⟩ := C0
  simp only [ctxSb, Ctx.mk.injEq, Env.mk.injEq, true_and]
  have : ∀ p ∈ VE, (p.1, (sbScheme s p.2.1, p.2.2)) = p := by
    intro p hp
    obtain ⟨x, ⟨bd, body⟩, st⟩ := p
    simp only [sbScheme, Prod.mk.injEq, Scheme.mk.injEq, true_and, and_true]
    refine sb_eq_self_iff.mpr fun a ha => hs _ (rigid_of_old (old_of_root_ve (C0 := ⟨T, U, ⟨QE, TE, VE⟩⟩) hp ha))
  simp only [sbVE]
  calc VE.map (fun p => (p.1, (sbScheme s p.2.1, p.2.2))) = VE.map id := List.map_congr_left this
    _ = VE := List.map_id VE

mutual
theorem wAtExp_sound (fuel n0 : Nat) : ∀ (a : BAtExp) (C : Ctx) (st : WSt) (r : Ty × AAtExp) (st' : WSt),
    SPre n0 C st → wAtExp fuel (rigidFrom n0) C a st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => checkAtExp (ctxSb s C) (sbAtExp s r.2) = true ∧ (sbAtExp s r.2).ty = sb s r.1)
  | .scon sc, C, st, r, st', hp, h => by
    cases sc with
    | int k =>
      simp only [wAtExp] at h
      obtain ⟨t, st1, h1, h2⟩ := wbind_ok h
      obtain ⟨rfl, rfl⟩ := freshC_ok h1
      obtain ⟨rfl, rfl⟩ := pure_ok' h2
      have P0 : PostK n0 C st st [] (fun s => checkAtExp (ctxSb s C) (.scon (.int k) (sb s (.var (.fresh st.n .num))))
          = true ∧ AAtExp.ty (.scon (.int k) (sb s (.var (.fresh st.n .num)))) = sb s (.var (.fresh st.n .num))) [] :=
        PostK.now hp (fun _ h => nomatch h) (fun _ h => nomatch h) fun s hs _ => ⟨by
          have ha : Adm .num (s (.fresh st.n .num)) := hs.resp (.fresh st.n .num)
          simp only [checkAtExp, sb]
          exact genAt_int ha, rfl⟩
      exact ⟨[], (P0.fresh (c := .num)).weaken (covSub fun τ hτ => by simpa using hτ) fun _ _ h => h⟩
    | float m e =>
      simp only [wAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨[], PostK.closed hp rfl fun s _ => by
        show checkAtExp _ (.scon _ (sb s tFloatTy)) = true ∧ AAtExp.ty (.scon _ (sb s tFloatTy)) = sb s tFloatTy
        rw [sb_closed rfl]; exact ⟨rfl, rfl⟩⟩
    | char c =>
      simp only [wAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨[], PostK.closed hp rfl fun s _ => by
        show checkAtExp _ (.scon _ (sb s tCharTy)) = true ∧ AAtExp.ty (.scon _ (sb s tCharTy)) = sb s tCharTy
        rw [sb_closed rfl]; exact ⟨rfl, rfl⟩⟩
    | str c =>
      simp only [wAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨[], PostK.closed hp rfl fun s _ => by
        show checkAtExp _ (.scon _ (sb s tStringTy)) = true ∧ AAtExp.ty (.scon _ (sb s tStringTy)) = sb s tStringTy
        rw [sb_closed rfl]; exact ⟨rfl, rfl⟩⟩
  | .var lv, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    cases hl : C.lookupVal lv with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wbind_ok h
      dsimp only at h2
      have hpi := post_inst hp (hp.ctxW _ _ _ hl) (lookup_facts hp hl).1 h1
      obtain ⟨rfl, rfl⟩ := pure_ok' h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg =>
        ⟨by simp only [checkAtExp, sbAtExp, (lookup_facts hp hl).2 s hs]; exact hg, rfl⟩⟩
  | .con lc, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wbind_ok h
      dsimp only at h2
      have hpi := post_inst hp (hp.ctxW _ _ _ hl) (lookup_facts hp hl).1 h1
      obtain ⟨rfl, rfl⟩ := pure_ok' h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg =>
        ⟨by simp only [checkAtExp, sbAtExp, (lookup_facts hp hl).2 s hs]; exact hg, rfl⟩⟩
  | .op o, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    cases hl : OTstat o with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wbind_ok h
      dsimp only at h2
      have hpi := post_inst hp (otstat_schW hl st.n) (fun c hc => by
        obtain ⟨h1, -, h3⟩ := mem_scheme_tyvars.mp hc
        exact absurd ((otstat_ok _ (find?_mem hl)).2 _ h1) h3) h1
      obtain ⟨rfl, rfl⟩ := pure_ok' h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg =>
        ⟨by simp only [checkAtExp, sbAtExp, hl]; rw [otstat_sbScheme hl hs] at hg; exact hg, rfl⟩⟩
  | .unit, C, st, r, st', hp, h => by
    simp only [wAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨[], PostK.closed hp rfl fun s _ => ⟨rfl, (sb_closed rfl).symm⟩⟩
  | .tuple e1 e2 e3, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨⟨τ2, a2⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
    obtain ⟨⟨τ3, a3⟩, st3, h3, k3⟩ := wbind_ok k2; dsimp only at k3
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e1 C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wExp_sound fuel n0 e2 C st1 _ st2 (hp.later P1.seg) h2
    have P12 := PostK.seqSame hp P1 P2
    obtain ⟨K3, P3⟩ := wExpOpt_sound fuel n0 e3 C st2 _ st3 (hp.later P12.seg) h3
    have P123 := PostK.seqSame hp P12 P3
    obtain ⟨rfl, rfl⟩ := pure_ok' k3
    refine ⟨_, P123.weaken cov_tuple fun s _ ⟨⟨⟨c1, t1⟩, ⟨c2, t2⟩⟩, ⟨c3, t3⟩⟩ => ?_⟩
    simp only at c1 t1 c2 t2 c3 t3
    simp only [checkAtExp, sbAtExp, c1, c2, c3, Bool.and_self, AAtExp.ty, t1, t2, t3, tupleTy_sb, true_and]
  | .nil, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    obtain ⟨α, st1, h1, h2⟩ := wbind_ok h
    obtain ⟨rfl, rfl⟩ := freshV_ok h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h2
    refine ⟨[], (PostK.start hp).fresh.weaken (cov_listTy fun v hv => ⟨_, by simp, hv⟩) fun s _ _ => ?_⟩
    simp [checkAtExp, sbAtExp, isListTy, listTy, sb, sbList, AAtExp.ty]
  | .record _, C, st, r, st', hp, h => by simp only [wAtExp] at h; cases h
  | .update _ _, C, st, r, st', hp, h => by simp only [wAtExp] at h; cases h
  | .letE d e, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    obtain ⟨ad, st1, h1, k1⟩ := wbind_ok h
    obtain ⟨θ, st1', h1', k1'⟩ := wbind_ok k1
    obtain ⟨hθ, e⟩ := getθ_ok h1'
    subst hθ; subst st1'
    obtain ⟨⟨Kd, PD⟩, hmono⟩ := wDec_sound fuel n0 d C st ad st1 hp h1
    cases ad with
    | val VE0 avb =>
    dsimp only at k1'
    obtain ⟨⟨τ, ae⟩, st2, h2, k2⟩ := wbind_ok k1'
    dsimp only at k2
    obtain ⟨rfl, rfl⟩ := pure_ok' k2
    simp only [ADec.env] at PD hmono
    have hi1 := PD.seg.inv
    have hθ1 : SOk n0 (lk st1.θ) := hi1.sok
    have hKk := kseg_clos (VE0 := VE0) hp PD.seg (fun τ hτ => (PD.okT τ hτ).1) PD.reach
    have PDk := (PD.withAbs.weaken (tys' := []) (covSub fun _ h => nomatch h) fun _ _ c => c).addK hKk
    -- the closure: schemes W can use, free variables free in θ1 C
    have hVEc : ∀ q ∈ closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0),
        SchW st1.n q.2.1 ∧ (∀ c, BVar.ty c ∈ q.2.1.tyvars → AnyV n0 c) ∧
        ∀ c, BVar.ty c ∈ q.2.1.tyvars → BVar.ty c ∈ (ctxSb (lk st1.θ) C).tyvars := by
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := closGroup_mem hmono hq
      have hb : q0.2.1.body ∈ veBodies VE0 := List.mem_map.mpr ⟨q0, hq0, rfl⟩
      have hok1 : OkT st1.n (sb (lk st1.θ) q0.2.1.body) := hi1.ok.okT (PD.okT _ hb).1
      have hto : TyOnly (sb (lk st1.θ) q0.2.1.body) := TyOnly.of_okT hok1
      refine ⟨closE_schW hok1, fun c hc => ?_, fun c hc => (closE_tyvars hto hc).2⟩
      exact anyT_sb PD.seg.any (PD.okT _ hb).2 c (closE_tyvars hto hc).1
    have hpB : SPre n0 (C.plusVE (closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0))) st1 :=
      hp.plusVE PD.seg.le hi1 PD.seg.any fun q hq => ⟨(hVEc q hq).1, (hVEc q hq).2.1⟩
    obtain ⟨Kb, PB⟩ := wExp_sound fuel n0 e _ st1 _ _ hpB h2
    -- a free variable of the closure: of the image of a free variable of C
    have hsrc : ∀ c, BVar.ty c ∈ (C.plusVE (closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0))).tyvars →
        ∀ b, TV b (lk st1.θ c) → ∃ c', BVar.ty c' ∈ C.tyvars ∧ TV b (lk st1.θ c') := by
      intro c hc b hb
      rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
      · exact ⟨c, hc, hb⟩
      · have hA := (hVEc q hq).2.2 c hcq
        rw [hp.A_fixed hθ1 hi1.good.idem hA] at hb
        simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
        exact hp.A_src hθ1 hA
    have hR : ∀ b, Reach (lk st1.θ) (C.plusVE (closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0))) st1.n b →
        Reach (lk st.θ) C st.n b := by
      rintro b (hb | ⟨c, hc, hb⟩)
      · exact .inl (new_of_new PD.seg.le hb)
      · obtain ⟨c', hc', hb'⟩ := hsrc c hc b hb
        exact reach_shrink PD.seg hp.inv hc' hb'
    have hAv : AvoidK (((ctxSb (lk st1.θ) C).tyvars, veBodies (sbVE (lk st1.θ) VE0)) :: Kd)
        (Reach (lk st1.θ) (C.plusVE (closGroup (ctxSb (lk st1.θ) C).tyvars (sbVE (lk st1.θ) VE0))) st1.n) := by
      rintro k hk b hg (hb | ⟨c, hc, hb⟩)
      · rw [(PDk.ks.zone k hk b hg).2] at hb; cases hb
      · obtain ⟨c', hc', hb'⟩ := hsrc c hc b hb
        exact PDk.ks.old k hk b hg c' (hp.old hc') hb'
    have P := PDk.seq PB hR hAv
    refine ⟨_, P.weaken (covSub fun τ hτ => by simpa using hτ) fun s hs ⟨⟨⟨cD, hab⟩, hdk⟩, cB, tB⟩ => ?_⟩
    have H : ClosHyp n0 C VE0 (lk st1.θ) s :=
      { isMono := hmono
        ok := fun q hq v hv => by
          obtain ⟨a, e', h1, -⟩ := (PD.okT _ (List.mem_map.mpr ⟨q, hq, rfl⟩)).1 v hv
          exact ⟨a, e', h1⟩
        θok := hθ1
        idem := hi1.good.idem
        sok := hs
        abs := hab
        dead := hdk
            (new_of_new hp.inv.le hz)
        ctxB := hp.ctxB
        ctxF := hp.ctxF
        rest := hp.rest }
    simp only at cD cB tB
    rw [ctxSb_plusVE, closGroup_sb H] at cB
    refine ⟨?_, ?_⟩
    · simp only [sbAtExp, checkAtExp, Bool.and_eq_true]
      refine ⟨cD, ?_⟩
      simp only [sbDec, ADec.result]
      exact cB
    · simp only [sbAtExp, AAtExp.ty]; exact tB
  | .paren e, C, st, r, st', hp, h => by
    simp only [wAtExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' k1
    exact ⟨_, P1.weaken (cov_refl _) fun s _ c => by simpa [checkAtExp, sbAtExp, AAtExp.ty] using c⟩
theorem wExp_sound (fuel n0 : Nat) : ∀ (e : BExp) (C : Ctx) (st : WSt) (r : Ty × AExp) (st' : WSt),
    SPre n0 C st → wExp fuel (rigidFrom n0) C e st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => checkExp (ctxSb s C) (sbExp s r.2) = true ∧ (sbExp s r.2).ty = sb s r.1)
  | .atexp a, C, st, r, st', hp, h => by
    simp only [wExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wAtExp_sound fuel n0 a C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' k1
    exact ⟨_, P1.weaken (cov_refl _) fun s _ c => by simpa [checkExp, sbExp, AExp.ty] using c⟩
  | .app e a, C, st, r, st', hp, h => by
    simp only [wExp] at h
    obtain ⟨⟨τ1, ae⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨⟨τ2, aa⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
    obtain ⟨β, st3, h3, k3⟩ := wbind_ok k2
    obtain ⟨rfl, rfl⟩ := freshV_ok h3
    obtain ⟨_, st4, h4, k4⟩ := wbind_ok k3
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wAtExp_sound fuel n0 a C st1 _ st2 (hp.later P1.seg) h2
    have P3 := (PostK.seqSame hp P1 P2).fresh
    have P4 := P3.unify (τ1 := τ1) (τ2 := .fn τ2 (.var (.fresh st2.n .any)))
      (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · simp only [Ty.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact ⟨τ2, by simp, hv⟩
          · exact ⟨.var (.fresh st2.n .any), by simp, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_ok' k4
    refine ⟨_, P4.weaken (covSub fun τ hτ => by simp at hτ; simp [hτ]) fun s _ ⟨⟨⟨c1, t1⟩, c2, t2⟩, he⟩ => ?_⟩
    simp only at c1 t1 c2 t2
    have hty : (sbExp s ae).ty = .fn (sbAtExp s aa).ty (sb s (.var (.fresh st2.n .any))) := by
      rw [t1, he, t2]; rfl
    simp only [checkExp, sbExp, c1, c2, Bool.true_and, hty, decide_true, AExp.ty, Ty.cod, and_self]
  | .lam p e, C, st, r, st', hp, h => by
    simp only [wExp] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
    obtain ⟨e1, P1⟩ := wAtPat_sound fuel n0 p C st _ st1 hp h1
    simp only at e1; subst e1
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
      ⟨(atpat_ve ap q hq).1, (atpat_ve ap q hq).2.2⟩
    obtain ⟨K2, P2⟩ := wExp_sound fuel n0 e _ st1 _ st2 hpB h2
    have P12 := P1.seq P2 hR hA
    obtain ⟨rfl, rfl⟩ := pure_ok' k2
    refine ⟨_, P12.weaken (cov_fn (fun v hv => by
        obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩)
      (fun v hv => ⟨τe, by simp, hv⟩)) fun s _ ⟨cp, ce, te⟩ => ?_⟩
    simp only at ce te
    rw [ctxSb_plusVE] at ce
    simp only [checkExp, sbExp, cp, sbAtPat_ve, ce, Bool.and_self, AExp.ty, sbAtPat_ty, te, sb, true_and]
  | .caseE e m, C, st, r, st', hp, h => by
    simp only [wExp] at h
    obtain ⟨⟨τe, ae⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨⟨τm, am⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
    obtain ⟨β, st3, h3, k3⟩ := wbind_ok k2
    obtain ⟨rfl, rfl⟩ := freshV_ok h3
    obtain ⟨_, st4, h4, k4⟩ := wbind_ok k3
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wMatch_sound fuel n0 m C st1 _ st2 (hp.later P1.seg) h2
    have P3 := (PostK.seqSame hp P1 P2).fresh
    have P4 := P3.unify (τ1 := τm) (τ2 := .fn τe (.var (.fresh st2.n .any)))
      (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · simp only [Ty.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact ⟨τe, by simp, hv⟩
          · exact ⟨.var (.fresh st2.n .any), by simp, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_ok' k4
    refine ⟨_, P4.weaken (covSub fun τ hτ => by simp at hτ; simp [hτ]) fun s _ ⟨⟨⟨c1, t1⟩, c2, t2⟩, he⟩ => ?_⟩
    simp only at c1 t1 c2 t2
    have hty : (sbMatch s am).ty = .fn (sbExp s ae).ty (sb s (.var (.fresh st2.n .any))) := by
      rw [t2, he, t1]; rfl
    simp only [checkExp, sbExp, c1, c2, Bool.true_and, hty, decide_true, AExp.ty, Ty.cod, and_self]
theorem wExpOpt_sound (fuel n0 : Nat) : ∀ (e : Option BExp) (C : Ctx) (st : WSt) (r : Option Ty × Option AExp)
    (st' : WSt), SPre n0 C st → wExpOpt fuel (rigidFrom n0) C e st = .ok r st' →
    Post n0 C st st' r.1.toList (fun s => checkExpOpt (ctxSb s C) (sbExpOpt s r.2) = true ∧
      AExp.tyOpt (sbExpOpt s r.2) = sbOpt s r.1)
  | none, C, st, r, st', hp, h => by
    simp only [wExpOpt] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨[], (PostK.start hp).weaken (covSub fun τ hτ => by simp at hτ) fun _ _ _ => ⟨rfl, rfl⟩⟩
  | some e, C, st, r, st', hp, h => by
    simp only [wExpOpt] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' k1
    exact ⟨_, P1.weaken (covSub fun τ hτ => by simpa using hτ) fun s _ c => by
      simpa [checkExpOpt, sbExpOpt, AExp.tyOpt, sbOpt] using c⟩
theorem wMatch_sound (fuel n0 : Nat) : ∀ (m : BMatch) (C : Ctx) (st : WSt) (r : Ty × AMatch) (st' : WSt),
    SPre n0 C st → wMatch fuel (rigidFrom n0) C m st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => checkMatch (ctxSb s C) (sbMatch s r.2) = true ∧ (sbMatch s r.2).ty = sb s r.1)
  | .mk mr rest, C, st, r, st', hp, h => by
    simp only [wMatch] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨ar, st2, h2, k2⟩ := wbind_ok k1
    obtain ⟨K1, P1⟩ := wMRule_sound fuel n0 mr C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wMatchOpt_sound fuel n0 rest C τ1 st1 ar st2 st [τ1] _ K1 hp P1 (by simp) h2
    obtain ⟨rfl, rfl⟩ := pure_ok' k2
    refine ⟨_, P2.weaken (cov_refl _) fun s _ ⟨⟨c1, t1⟩, c2⟩ => ?_⟩
    simp only at c1 t1
    simp only [checkMatch, sbMatch, c1, Bool.true_and, AMatch.ty, and_true]
    rw [t1]; exact ⟨c2, rfl⟩
theorem wMatchOpt_sound (fuel n0 : Nat) : ∀ (m : Option BMatch) (C : Ctx) (τ : Ty) (st1 : WSt) (r : Option AMatch)
    (st2 : WSt) (st0 : WSt) (tys : List Ty) (Chk : FSub → Prop) (K : List ConW),
    SPre n0 C st0 → PostK n0 C st0 st1 tys Chk K → τ ∈ tys →
    wMatchOpt fuel (rigidFrom n0) C τ m st1 = .ok r st2 →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ checkMatchOptAt (ctxSb s C) (sb s τ) (sbMatchOpt s r) = true)
  | none, C, τ, st1, r, st2, st0, tys, Chk, K, hp, P0, hτ, h => by
    simp only [wMatchOpt] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨K, P0.weaken (cov_refl _) fun s _ c => ⟨c, rfl⟩⟩
  | some m, C, τ, st1, r, st2, st0, tys, Chk, K, hp, P0, hτ, h => by
    simp only [wMatchOpt] at h
    obtain ⟨⟨τm, am⟩, st3, h3, k3⟩ := wbind_ok h; dsimp only at k3
    obtain ⟨_, st4, h4, k4⟩ := wbind_ok k3
    obtain ⟨K1, P1⟩ := wMatch_sound fuel n0 m C st1 _ st3 (hp.later P0.seg) h3
    have P01 := PostK.seqSame hp P0 P1
    have P2 := P01.unify (τ1 := τm) (τ2 := τ) (fun x hx v hv => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨x, by simp, hv⟩
      · exact ⟨x, List.mem_append_left _ hτ, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_ok' k4
    refine ⟨_, P2.weaken (covSub fun τ' hτ' => List.mem_append_left _ hτ') fun s _ ⟨⟨c0, c1, t1⟩, he⟩ => ⟨c0, ?_⟩⟩
    simp only at c1 t1
    simp only [checkMatchOptAt, sbMatchOpt, c1, Bool.true_and, decide_eq_true_eq, t1, he]
theorem wMRule_sound (fuel n0 : Nat) : ∀ (mr : BMRule) (C : Ctx) (st : WSt) (r : Ty × AMRule) (st' : WSt),
    SPre n0 C st → wMRule fuel (rigidFrom n0) C mr st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => checkMRule (ctxSb s C) (sbMRule s r.2) = true ∧ (sbMRule s r.2).ty = sb s r.1)
  | .mk p e, C, st, r, st', hp, h => by
    simp only [wMRule] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p C st _ st1 hp h1
    simp only at e1; subst e1
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
      ⟨(pat_ve ap q hq).1, (pat_ve ap q hq).2.2⟩
    obtain ⟨K2, P2⟩ := wExp_sound fuel n0 e _ st1 _ st2 hpB h2
    have P12 := P1.seq P2 hR hA
    obtain ⟨rfl, rfl⟩ := pure_ok' k2
    refine ⟨_, P12.weaken (cov_fn (fun v hv => by
        obtain ⟨τ', h1', h2'⟩ := pat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩)
      (fun v hv => ⟨τe, by simp, hv⟩)) fun s _ ⟨cp, ce, te⟩ => ?_⟩
    simp only at ce te
    rw [ctxSb_plusVE] at ce
    simp only [checkMRule, sbMRule, cp, sbPat_ve, ce, Bool.and_self, AMRule.ty, sbPat_ty, te, sb, true_and]
theorem wDec_sound (fuel n0 : Nat) : ∀ (d : BDec) (C : Ctx) (st : WSt) (r : ADec) (st' : WSt),
    SPre n0 C st → wDec fuel (rigidFrom n0) C d st = .ok r st' →
    Post n0 C st st' (veBodies r.env) (fun s => checkDec (ctxSb s C) (sbDec s r) = true) ∧
      ∀ q ∈ r.env, q.2.1.bound = []
  | .val (.pat p e), C, st, r, st', hp, h => by
    simp only [wDec] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wbind_ok h; dsimp only at k1
    by_cases hsh : (ap.ve.all fun q => !conBound C q.1) = true
    · rw [if_pos hsh] at k1
      obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wbind_ok k1; dsimp only at k2
      obtain ⟨_, st3, h3, k3⟩ := wbind_ok k2
      obtain ⟨e1, P1⟩ := wAtPat_sound fuel n0 p C st _ st1 hp h1
      simp only at e1; subst e1
      obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
        ⟨(atpat_ve ap q hq).1, (atpat_ve ap q hq).2.2⟩
      obtain ⟨K2, P2⟩ := wExp_sound fuel n0 e _ st1 _ st2 hpB h2
      have P3 := (P1.seq P2 hR hA).unify (τ1 := τe) (τ2 := ap.ty) (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩) h3
      obtain ⟨rfl, rfl⟩ := pure_ok' k3
      refine ⟨⟨_, P3.weaken ?_ fun s _ ⟨⟨cp, ce, te⟩, he⟩ => ?_⟩, fun q hq => (atpat_ve ap q hq).1⟩
      · intro x hx v hv
        simp only [ADec.env, veBodies, List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        obtain ⟨τ', h1', h2'⟩ := (atpat_ve ap q hq).2.2 v hv
        exact ⟨τ', List.mem_append_left _ h1', h2'⟩
      · simp only at ce te
        rw [ctxSb_plusVE] at ce
        simp only [ADec.env, checkDec, sbDec]
        rw [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨?_, by simp [sbValBind, AValBind.ve, sbAtPat_ve]⟩
        simp only [sbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨checkAtPat_lkC (lkC_noShadow hsh) _ cp, ce⟩, by rw [te, he, sbAtPat_ty]⟩
    · rw [if_neg hsh] at k1; cases k1
  | .val (.var x ann e rest), C, st, r, st', hp, h => by
    simp only [wDec] at h
    obtain ⟨es, st1, h1, k1⟩ := wbind_ok h
    obtain ⟨avb, st2, h2, k2⟩ := wbind_ok k1
    obtain ⟨hes, PG⟩ := groupEntries_sound _ st es st1 hp h1
    have hmono := groupVE_mono (.var x ann e rest) es (fun e he => (hes e he).1)
    obtain ⟨⟨K2, PM⟩, hve, hann⟩ := wMembers_sound fuel n0 (.var x ann e rest) _ es st1 avb st2 C
      (groupVE (.var x ann e rest) es) st (es.map (·.2)) _ _ h2 rfl hp PG
      (fun q hq => ⟨(hmono q hq).1, by
        obtain ⟨-, -, e', he', hb⟩ := hmono q hq; rw [hb]; exact List.mem_map_of_mem he'⟩)
      (fun e' he' => ⟨List.mem_map_of_mem he', (hes e' he').1, (hes e' he').2⟩)
    obtain ⟨rfl, rfl⟩ := pure_ok' k2
    refine ⟨⟨K2, PM.weaken ?_ fun s _ ⟨_, cv⟩ => ?_⟩, fun q hq => (hmono q hq).1⟩
    · intro x' hx v hv
      simp only [ADec.env, veBodies, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨-, -, e', he', hb⟩ := hmono q hq
      exact ⟨e'.2, List.mem_map_of_mem he', by rw [← hb]; exact hv⟩
    · simp only [checkDec, sbDec, Bool.and_eq_true, decide_eq_true_eq]
      rw [← ctxSb_plusVE]
      exact ⟨cv, by rw [valbind_ve_sb s avb hann, hve]⟩
theorem wMembers_sound (fuel n0 : Nat) : ∀ (vb : BValBind) (Cg : Ctx) (es : List (Option (BTy × List BVar) × Ty))
    (st1 : WSt) (avb : AValBind) (st2 : WSt) (C : Ctx) (VE0 : ValEnv) (st0 : WSt) (tys : List Ty)
    (Chk : FSub → Prop) (K : List ConW),
    wMembers fuel (rigidFrom n0) Cg vb es st1 = .ok avb st2 → Cg = C.plusVE VE0 → SPre n0 C st0 →
    PostK n0 C st0 st1 tys Chk K → (∀ q ∈ VE0, q.2.1.bound = [] ∧ q.2.1.body ∈ tys) →
    (∀ e ∈ es, e.2 ∈ tys ∧ annU e.1 = [] ∧ ∀ (C' : Ctx) (s : FSub), C'.U = C.U →
      (∀ lc, C'.lookupTy lc = C.lookupTy lc) → checkAnn C' e.1 (sb s e.2) = true) →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ checkValBind (ctxSb s Cg) (sbValBind s avb) = true) ∧
      avb.ve = groupVE vb es ∧ AnnNilV avb
  | .var x _ e rest, Cg, (ann, τx) :: es, st1, avb, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    subst hCg
    simp only [wMembers] at h
    obtain ⟨⟨τe, ae⟩, st3, h3, k3⟩ := wbind_ok h; dsimp only at k3
    obtain ⟨_, st4, h4, k4⟩ := wbind_ok k3
    obtain ⟨ar, st5, h5, k5⟩ := wbind_ok k4
    obtain ⟨hτx, hann, hck⟩ := hes _ (.head _)
    rw [hann, plusU_nil] at h3
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := VE0) hp P0 fun q hq =>
      ⟨(hVE q hq).1, fun v hv => ⟨_, (hVE q hq).2, hv⟩⟩
    obtain ⟨K1, P1⟩ := wExp_sound fuel n0 e _ st1 _ st3 hpB h3
    have P2 := (P0.seq P1 hR hA).unify (τ1 := τe) (τ2 := τx) (fun x' hx v hv => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨x', by simp, hv⟩
      · exact ⟨x', List.mem_append_left _ hτx, hv⟩) h4
    have P2' := P2.weaken (covSub fun τ' hτ' => List.mem_append_left _ hτ') fun _ _ c => c
    obtain ⟨⟨K3, P3⟩, hst⟩ := wMembersOpt_sound fuel n0 rest _ es st4 ar st5 C VE0 st0 tys _ _ h5 rfl hp P2' hVE
      (fun e' he' => hes e' (.tail _ he'))
    obtain ⟨rfl, rfl⟩ := pure_ok' k5
    refine ⟨⟨K3, P3.weaken (cov_refl _) fun s _ ⟨⟨⟨c0, ce, te⟩, he⟩, cr⟩ => ⟨c0, ?_⟩⟩, ?_, ?_⟩
    · simp only at ce te
      simp only [checkValBind, sbValBind, Bool.and_eq_true, decide_eq_true_eq, hann, plusU_nil, ce, cr, and_true,
        true_and]
      refine ⟨hck _ s rfl (fun lc => rfl), ?_⟩
      rw [te, he]
    · cases rest with
      | none => cases ar with
        | none => simp [AValBind.ve, groupVE]
        | some _ => exact absurd hst id
      | some vb => cases ar with
        | none => exact absurd hst id
        | some avb' => simp only [AValBind.ve, groupVE, hst.1]
    · unfold AnnNilV
      refine ⟨hann, ?_⟩
      cases rest with
      | none => cases ar with
        | none => trivial
        | some _ => exact absurd hst id
      | some vb => cases ar with
        | none => exact absurd hst id
        | some avb' => exact hst.2
  | .var _ _ _ _, Cg, [], st1, avb, st2, C, VE0, st0, tys, Chk, K, h, _, _, _, _, _ => by
    simp only [wMembers] at h; cases h
  | .pat _ _, Cg, es, st1, avb, st2, C, VE0, st0, tys, Chk, K, h, _, _, _, _, _ => by
    simp only [wMembers] at h; cases h
theorem wMembersOpt_sound (fuel n0 : Nat) : ∀ (vb : Option BValBind) (Cg : Ctx)
    (es : List (Option (BTy × List BVar) × Ty)) (st1 : WSt) (r : Option AValBind) (st2 : WSt) (C : Ctx)
    (VE0 : ValEnv) (st0 : WSt) (tys : List Ty) (Chk : FSub → Prop) (K : List ConW),
    wMembersOpt fuel (rigidFrom n0) Cg vb es st1 = .ok r st2 → Cg = C.plusVE VE0 → SPre n0 C st0 →
    PostK n0 C st0 st1 tys Chk K → (∀ q ∈ VE0, q.2.1.bound = [] ∧ q.2.1.body ∈ tys) →
    (∀ e ∈ es, e.2 ∈ tys ∧ annU e.1 = [] ∧ ∀ (C' : Ctx) (s : FSub), C'.U = C.U →
      (∀ lc, C'.lookupTy lc = C.lookupTy lc) → checkAnn C' e.1 (sb s e.2) = true) →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ checkValBindOpt (ctxSb s Cg) (sbValBindOpt s r) = true) ∧
      (match vb, r with
       | none, none => True
       | some vb, some avb => avb.ve = groupVE vb es ∧ AnnNilV avb
       | _, _ => False)
  | none, Cg, es, st1, r, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    simp only [wMembersOpt] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨⟨K, P0.weaken (cov_refl _) fun s _ c => ⟨c, rfl⟩⟩, trivial⟩
  | some vb, Cg, es, st1, r, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    simp only [wMembersOpt] at h
    obtain ⟨a, st3, h3, k3⟩ := wbind_ok h
    obtain ⟨⟨K1, P1⟩, hve, hann⟩ := wMembers_sound fuel n0 vb Cg es st1 a st3 C VE0 st0 tys Chk K h3 hCg hp P0 hVE hes
    obtain ⟨rfl, rfl⟩ := pure_ok' k3
    exact ⟨⟨K1, P1.weaken (cov_refl _) fun s _ c => by simpa [checkValBindOpt, sbValBindOpt] using c⟩, hve, hann⟩
end

end StandardElm.Stat.Complete
