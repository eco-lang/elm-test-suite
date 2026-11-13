/-
  A Standard Definition of Elm? Mechanisation: L10 with records and rows (plan step 11,
  milestone (d)): the induction over W for expressions, rows of fields, matches, declarations
  and groups (WSoundExp.lean for `inferExpWD`). What a call returns is accepted by the checker
  under every later substitution `s` that fixes the rigid variables, absorbs the call's final
  substitution and respects the closures taken inside, once a canonical `U` absorbing `s` is
  given (with the constructor witnesses of the result).

  New cases: a record expression (its type is the record of its fields' types, `Row.modify`
  commuting with the substitution); an update `{x | l = e}` (the unification gives `s τx =
  s ⟨ρ | ε⟩`, a canonical record whose merged row has the fields' row as a sub-row); the closure
  at a `let` with row variables (`closGroup_rsb`). The canonicity a unification needs is that of
  its two types under the substitution of that moment, from `s` (or, for a fresh variable,
  trivially).
-/
import StandardElmMech.Stat.Complete.WDSoundAux

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

namespace WDS

/-- The check of a phrase under `s`, given a canonical `U` absorbing `s`. -/
abbrev XCk (n0 : Nat) (s : RSub) (l : List Ty) (W : RSub → Prop) (P : Prop) : Prop :=
  ∀ U, GoodU n0 U s → CnL U l → W U → P

section cnS
variable {n0 : Nat} {s U : RSub} (hs : SOk n0 s) (hU : GoodU n0 U s)
include hs hU

theorem cnS_atexp {a : AAtExp} (h : CnL U (tysAtExp false a)) : cnB (rsbAtExp s a).ty = true :=
  cn_atexp_ty _ fun τ hτ => by
    rw [tysAtExp_sbD false s (fix_bnd0D hs.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact hU.cn (h σ hσ)

theorem cnS_exp {e : AExp} (h : CnL U (tysExp false e)) : cnB (rsbExp s e).ty = true :=
  cn_exp_ty _ fun τ hτ => by
    rw [tysExp_sbD false s (fix_bnd0D hs.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact hU.cn (h σ hσ)

theorem cnS_match {m : AMatch} (h : CnL U (tysMatch false m)) : cnB (rsbMatch s m).ty = true :=
  cn_match_ty _ fun τ hτ => by
    rw [tysMatch_sbD false s (fix_bnd0D hs.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact hU.cn (h σ hσ)

theorem cnS_mrule {mr : AMRule} (h : CnL U (tysMRule false mr)) : cnB (rsbMRule s mr).ty = true :=
  cn_mrule_ty _ fun τ hτ => by
    rw [tysMRule_sbD false s (fix_bnd0D hs.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact hU.cn (h σ hσ)

theorem cnS_exprow {r : AExpRow} (h : CnL U (tysExpRow false r)) : CnRow (rsbExpRow s r).row :=
  cn_exprow_row _ fun τ hτ => by
    rw [tysExpRow_sbD false s (fix_bnd0D hs.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact hU.cn (h σ hσ)

end cnS

theorem cn_th {s θ : RSub} (h : AbsS s θ) {τ : Ty} (hc : cnB (rsb s τ) = true) : cnB (rsb θ τ) = true :=
  cnB_of_rsb (s := s) (by rw [absS_rsb h]; exact hc)

theorem cn_fresh_th {n0 : Nat} {st : WDSt} (hi : SInvW n0 st) {c : Cls} {k : Nat} (hk : st.n ≤ k) :
    cnB (rsb (th st) (.var (.fresh k c))) = true := by
  show cnB ((th st).img (.ty (.fresh k c))) = true
  rw [hi.unbound_new (by simp [newB, TyVar.isNew]; omega)]; rfl

theorem otstat_rsbScheme {o : Op} {σ : Scheme} {x : IdStatus} (h : OTstat o = some (σ, x)) {n0 : Nat} {s : RSub}
    (hs : SOk n0 s) : rsbScheme s σ = σ := by
  obtain ⟨hb, hv⟩ := otstat_ok _ (find?_mem h)
  obtain ⟨bd, body⟩ := σ
  simp only [rsbScheme, Scheme.mk.injEq, true_and]
  exact rsb_eq_self fun w hw => hs.bnd (hb _ (hv _ hw))

theorem ctxRsb_rootD {C0 : Ctx} {s : RSub} (hs : FixR (rigidFromD (freshAboveD C0)) s) : ctxRsb s C0 = C0 := by
  obtain ⟨T, U, ⟨QE, TE, VE⟩⟩ := C0
  simp only [ctxRsb, Ctx.mk.injEq, Env.mk.injEq, true_and]
  have : ∀ p ∈ VE, (p.1, (rsbScheme s p.2.1, p.2.2)) = p := by
    intro p hp
    obtain ⟨x, ⟨bd, body⟩, st⟩ := p
    simp only [rsbScheme, Prod.mk.injEq, Scheme.mk.injEq, true_and, and_true]
    exact rsb_eq_self fun w hw => hs w (rigid_of_oldD (old_of_root_veD (C0 := ⟨T, U, ⟨QE, TE, VE⟩⟩) hp hw))
  simp only [rsbVE]
  calc VE.map (fun p => (p.1, (rsbScheme s p.2.1, p.2.2))) = VE.map id := List.map_congr_left this
    _ = VE := List.map_id VE

/-- An entry of the closure W takes at a `let`. -/
theorem closGroup_memD {A : List BVar} {θ : RSub} {VE0 : ValEnv} (hm : ∀ q ∈ VE0, q.2.1.bound = [])
    {q : String × (Scheme × IdStatus)} (hq : q ∈ closGroup A (rsbVE θ VE0)) :
    ∃ q0 ∈ VE0, q = (q0.1, closE A (rsbVE θ VE0) (mono (rsb θ q0.2.1.body)), q0.2.2) := by
  rw [closGroup_eq] at hq
  simp only [FMap.mapV, rsbVE, List.map_map, List.mem_map, Function.comp] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  refine ⟨q0, hq0, ?_⟩
  obtain ⟨x, ⟨bd, τ⟩, st⟩ := q0
  have : bd = [] := hm _ hq0
  subst this
  rfl

theorem rowOpt_ty_modify (s : RSub) (l : Lab) (τ : Ty) (ρ : Row) :
    rsbRow s (Row.modify [(l, τ)] ρ) = Row.modify [(l, rsb s τ)] (rsbRow s ρ) := by
  rw [rsbRow_modifyD]; rfl

theorem sorted_modify_single {l : Lab} {τ : Ty} {ρ : Row} (h : Sorted ρ) : Sorted (Row.modify [(l, τ)] ρ) :=
  sorted_modify1 h

theorem cov_tuple' {τ1 τ2 : Ty} {τ3 : Option Ty} : Cov [tupleTy τ1 τ2 τ3] ([τ1] ++ [τ2] ++ τ3.toList) := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  rcases vars_tupleTy hv with h | h | ⟨τ, rfl, h⟩
  · exact ⟨τ1, by simp, h⟩
  · exact ⟨τ2, by simp, h⟩
  · exact ⟨τ, by simp, h⟩

theorem cov_fnD {τ1 τ2 : Ty} {l : List Ty} (h1 : ∀ v ∈ τ1.vars, ∃ τ ∈ l, v ∈ τ.vars)
    (h2 : ∀ v ∈ τ2.vars, ∃ τ ∈ l, v ∈ τ.vars) : Cov [Ty.fn τ1 τ2] l := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  simp only [Ty.vars, List.mem_append] at hv
  rcases hv with hv | hv
  · exact h1 v hv
  · exact h2 v hv

mutual
theorem wdAtExp_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (a : BAtExp) (C : Ctx) (st : WDSt) (r : Ty × AAtExp) (st' : WDSt),
    SPre n0 L C st → wdAtExp fuel (rigidFromD n0) C a st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => XCk n0 s (tysAtExp false r.2) (fun U => CWAtExp L U r.2)
      (checkAtExp (ctxRsb s C) (rsbAtExp s r.2) = true ∧ (rsbAtExp s r.2).ty = rsb s r.1))
  | .scon sc, C, st, r, st', hp, h => by
    cases sc with
    | int k =>
      simp only [wdAtExp] at h
      obtain ⟨t, st1, h1, h2⟩ := wdbind_ok h
      obtain ⟨rfl, rfl⟩ := freshCD_ok h1
      obtain ⟨rfl, rfl⟩ := pure_okD h2
      have P0 : PostK n0 C st st [] (fun s => XCk n0 s (tysAtExp false (.scon (.int k) (.var (.fresh st.n .num))))
          (fun U => CWAtExp L U (.scon (.int k) (.var (.fresh st.n .num))))
          (checkAtExp (ctxRsb s C) (rsbAtExp s (.scon (.int k) (.var (.fresh st.n .num)))) = true ∧
            (rsbAtExp s (.scon (.int k) (.var (.fresh st.n .num)))).ty = rsb s (.var (.fresh st.n .num)))) [] :=
        PostK.now hp (fun _ h => nomatch h) (fun _ h => nomatch h) fun s hs _ _ _ _ _ => ⟨by
          have ha : Adm .num (s.t (.fresh st.n .num)) := hs.resp (.fresh st.n .num)
          simp only [checkAtExp, rsbAtExp, rsb]
          exact genAt_int ha, rfl⟩
      exact ⟨[], (P0.freshC .num).weaken (covSub fun τ hτ => by simpa using hτ) fun _ _ h => h⟩
    | float m e =>
      simp only [wdAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨[], PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtExp _ (.scon _ (rsb s tFloatTy)) = true ∧ AAtExp.ty (.scon _ (rsb s tFloatTy)) = rsb s tFloatTy
        rw [rsb_closedD rfl]; exact ⟨rfl, rfl⟩⟩
    | char c =>
      simp only [wdAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨[], PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtExp _ (.scon _ (rsb s tCharTy)) = true ∧ AAtExp.ty (.scon _ (rsb s tCharTy)) = rsb s tCharTy
        rw [rsb_closedD rfl]; exact ⟨rfl, rfl⟩⟩
    | str c =>
      simp only [wdAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
      exact ⟨[], PostK.closed hp rfl fun s _ _ _ _ _ => by
        show checkAtExp _ (.scon _ (rsb s tStringTy)) = true ∧ AAtExp.ty (.scon _ (rsb s tStringTy)) = rsb s tStringTy
        rw [rsb_closedD rfl]; exact ⟨rfl, rfl⟩⟩
  | .var lv, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    cases hl : C.lookupVal lv with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wdbind_ok h
      dsimp only at h2
      have hpi := post_instD hp (hp.ctxW _ _ _ hl) (lookup_factsD hp hl).1 h1
      obtain ⟨rfl, rfl⟩ := pure_okD h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg U hU hcn _ =>
        ⟨by simp only [checkAtExp, rsbAtExp, (lookup_factsD hp hl).2 s hs]
            exact hg (hU.cn (hcn _ (List.mem_singleton_self _))), rfl⟩⟩
  | .con lc, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wdbind_ok h
      dsimp only at h2
      have hpi := post_instD hp (hp.ctxW _ _ _ hl) (lookup_factsD hp hl).1 h1
      obtain ⟨rfl, rfl⟩ := pure_okD h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg U hU hcn _ =>
        ⟨by simp only [checkAtExp, rsbAtExp, (lookup_factsD hp hl).2 s hs]
            exact hg (hU.cn (hcn _ (List.mem_singleton_self _))), rfl⟩⟩
  | .op o, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    cases hl : OTstat o with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wdbind_ok h
      dsimp only at h2
      have hpi := post_instD hp (otstat_schWD hl st.n) (fun c hc => by
        obtain ⟨h1, -, h3⟩ := mem_scheme_tyvars.mp hc
        exact absurd ((otstat_ok _ (find?_mem hl)).2 _ h1) h3) h1
      obtain ⟨rfl, rfl⟩ := pure_okD h2
      exact ⟨[], hpi.weaken (cov_refl _) fun s hs hg U hU hcn _ =>
        ⟨by simp only [checkAtExp, rsbAtExp, hl]
            have := hg (hU.cn (hcn _ (List.mem_singleton_self _)))
            rw [otstat_rsbScheme hl hs] at this; exact this, rfl⟩⟩
  | .unit, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨[], PostK.closed hp rfl fun s _ _ _ _ _ => ⟨rfl, (rsb_closedD rfl).symm⟩⟩
  | .tuple e1 e2 e3, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨τ2, a2⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨⟨τ3, a3⟩, st3, h3, k3⟩ := wdbind_ok k2; dsimp only at k3
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e1 C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wdExp_sound fuel n0 hL e2 C st1 _ st2 (hp.later P1.seg) h2
    have P12 := PostK.seqSame hp P1 P2
    obtain ⟨K3, P3⟩ := wdExpOpt_sound fuel n0 hL e3 C st2 _ st3 (hp.later P12.seg) h3
    have P123 := PostK.seqSame hp P12 P3
    obtain ⟨rfl, rfl⟩ := pure_okD k3
    refine ⟨_, P123.weaken cov_tuple' fun s _ ⟨⟨c1, c2⟩, c3⟩ U hU hcn ⟨w1, w2, w3⟩ => ?_⟩
    simp only [tysAtExp] at hcn
    obtain ⟨c1, t1⟩ := c1 U hU (hcn.sub fun τ hτ => by simp [hτ]) w1
    obtain ⟨c2, t2⟩ := c2 U hU (hcn.sub fun τ hτ => by simp [hτ]) w2
    obtain ⟨c3, t3⟩ := c3 U hU (hcn.sub fun τ hτ => by simp [hτ]) w3
    simp only at c1 t1 c2 t2 c3 t3
    simp only [checkAtExp, rsbAtExp, c1, c2, c3, Bool.and_self, AAtExp.ty, t1, t2, t3, tupleTy_sbD, true_and]
  | .nil, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    obtain ⟨α, st1, h1, h2⟩ := wdbind_ok h
    obtain ⟨rfl, rfl⟩ := freshVD_ok h1
    obtain ⟨rfl, rfl⟩ := pure_okD h2
    refine ⟨[], (PostK.start hp).fresh.weaken (cov_listTyD fun v hv => ⟨_, by simp, hv⟩) fun s _ _ _ _ _ _ => ?_⟩
    simp [checkAtExp, rsbAtExp, isListTy, listTy, rsb, rsbList, AAtExp.ty]
  | .record row, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    obtain ⟨⟨ρ, ar⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨K1, P1⟩, -⟩ := wdExpRowOpt_sound fuel n0 hL row C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD k1
    refine ⟨_, P1.weaken ?_ fun s _ c U hU hcn hw => ?_⟩
    · intro x hx v hv
      simp only [List.mem_singleton] at hx; subst hx
      simp only [Ty.vars] at hv
      obtain ⟨p, hp', hvp⟩ := mem_rowVarsR.mp hv
      exact ⟨p.2, List.mem_map_of_mem hp', hvp⟩
    · obtain ⟨c1, t1⟩ := c U hU hcn hw
      simp only at c1 t1
      refine ⟨by simpa [checkAtExp, rsbAtExp] using c1, ?_⟩
      simp only [rsbAtExp, AAtExp.ty, rsb, RSub.tl, mrg_nil_right, t1]
  | .update x row, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    cases hl : C.lookupVal ⟨none, x⟩ with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, xs⟩ := p
      rw [hl] at h; dsimp only at h
      obtain ⟨⟨ts, τx⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
      obtain ⟨⟨ρ, ar⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
      obtain ⟨e, st3, h3, k3⟩ := wdbind_ok k2
      obtain ⟨rfl, rfl⟩ := freshRowD_ok h3
      obtain ⟨_, st4, h4, k4⟩ := wdbind_ok k3
      obtain ⟨rfl, rfl⟩ := pure_okD k4
      have hpi := post_instD hp (hp.ctxW _ _ _ hl) (lookup_factsD hp hl).1 h1
      obtain ⟨⟨K2, P2⟩, hsort⟩ := wdExpRow_sound fuel n0 hL row C st1 _ st2 (hp.later hpi.seg) h2
      have P12 := (PostK.seqSame hp hpi P2).freshRow
      have hc : Cov [τx, .record ρ (some (.fresh st2.n))] ([τx] ++ ρ.map (·.2) ++ [.record [] (some (.fresh st2.n))]) := by
        intro y hy v hv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl
        · exact ⟨y, by simp, hv⟩
        · rw [vars_record] at hv
          rcases List.mem_append.mp hv with hv | hv
          · obtain ⟨p, hp', hvp⟩ := mem_rowVarsR.mp hv
            exact ⟨p.2, by simp [List.mem_map_of_mem hp'], hvp⟩
          · refine ⟨.record [] (some (.fresh st2.n)), by simp, ?_⟩
            simp only [tailVars, List.mem_singleton] at hv; subst hv; simp [Ty.vars, Ty.rowVars]
      have P3 := P12.unify hc h4
      have hi3 := P12.seg.inv
      refine ⟨_, P3.weaken (covSub fun τ hτ => by simp at hτ; simp [hτ]) fun s hs ⟨⟨hg, cr⟩, hab3, he⟩ U hU hcn hw => ?_⟩
      simp only [tysAtExp] at hcn
      have hcnx : cnB (rsb s τx) = true := hU.cn (hcn _ (List.mem_cons_self ..))
      obtain ⟨c2, t2⟩ := cr U hU (hcn.sub fun τ hτ => List.mem_cons_of_mem _ hτ) hw
      simp only at c2 t2
      have hrow := cnS_exprow hs hU (hcn.sub fun τ hτ => List.mem_cons_of_mem _ hτ)
      rw [t2] at hrow
      have heq : rsb s τx = rsb s (.record ρ (some (.fresh st2.n))) := by
        refine he (cn_th hab3 hcnx) ?_
        show cnB (rsb (th { st2 with n := st2.n + 1 }) (.record ρ (some (.fresh st2.n)))) = true
        have hfr : (th { st2 with n := st2.n + 1 }).r (.fresh st2.n) = ([], some (.fresh st2.n)) := by
          have := P2.seg.inv.unbound_new (v := .row (.fresh st2.n)) (by simp [newB])
          exact fix_row this
        rw [rsb, RSub.tl, hfr, mrg_nil_right, cnB_record]
        refine ⟨(sorted_rsbRow_iff _).mpr hsort, fun p hp' => ?_⟩
        obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hp'
        have : cnB (rsb s q.2) = true := hrow.2 (q.1, rsb s q.2) (mem_rsbRow.mpr ⟨q, hq, rfl⟩)
        exact cn_th hab3 this
      refine ⟨?_, rfl⟩
      simp only [checkAtExp, rsbAtExp, (lookup_factsD hp hl).2 s hs, hg hcnx, c2, Bool.true_and, Bool.and_eq_true]
      rw [heq]
      refine ⟨by simp [rsb, isRecordTy], ?_⟩
      rw [t2]
      have hc' := heq ▸ hcnx
      simp only [rsb, RSub.tl] at hc' ⊢
      exact subB_mrg (cnB_record.mp hc').1
  | .letE d e, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    obtain ⟨ad, st1, h1, k1⟩ := wdbind_ok h
    obtain ⟨θ, st1', h1', k1'⟩ := wdbind_ok k1
    obtain ⟨hθ, e'⟩ := getθD_ok h1'
    subst hθ; subst st1'
    obtain ⟨⟨Kd, PD⟩, hmono⟩ := wdDec_sound fuel n0 hL d C st ad st1 hp h1
    cases ad with
    | val VE0 avb =>
    dsimp only at k1'
    obtain ⟨⟨τ, ae⟩, st2, h2, k2⟩ := wdbind_ok k1'
    dsimp only at k2
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    simp only [ADec.env] at PD hmono
    have hi1 := PD.seg.inv
    have hθ1 : SOk n0 (th st1) := hi1.sok
    have hKk := kseg_closD (VE0 := VE0) hp PD.seg (fun τ hτ => PD.okT τ hτ) PD.reach
    have PDk := (PD.withAbs.weaken (tys' := []) (covSub fun _ h => nomatch h) fun _ _ c => c).addK hKk
    have hVEc : ∀ q ∈ closGroup (ctxRsb (th st1) C).tyvars (rsbVE (th st1) VE0),
        SchWD st1.n q.2.1 ∧ q.2.2 = .v ∧ ∀ c ∈ q.2.1.tyvars, c ∈ (ctxRsb (th st1) C).tyvars := by
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := closGroup_memD (fun q hq => (hmono q hq).1) hq
      have hb : q0.2.1.body ∈ veBodies VE0 := List.mem_map.mpr ⟨q0, hq0, rfl⟩
      have hok1 : OkTD st1.n (rsb (th st1) q0.2.1.body) := fun v hv => by
        obtain ⟨u, hu, hvu⟩ := (mem_vars_rsb _ _ v).mp hv
        exact ⟨hi1.nb u (PD.okT _ hb u hu).1 v hvu, (img_vars hi1.inv.good (PD.okT _ hb).old v hv).2⟩
      exact ⟨closE_schWD hok1, (hmono q0 hq0).2, fun c hc => (closE_tyvarsD hc).2⟩
    have hpB : SPre n0 L (C.plusVE (closGroup (ctxRsb (th st1) C).tyvars (rsbVE (th st1) VE0))) st1 :=
      hp.plusVE PD.seg.le hi1 (fun q hq => (hVEc q hq).1) (fun q hq => (hVEc q hq).2.1)
    obtain ⟨Kb, PB⟩ := wdExp_sound fuel n0 hL e _ st1 _ _ hpB h2
    have hsrc : ∀ c ∈ (C.plusVE (closGroup (ctxRsb (th st1) C).tyvars (rsbVE (th st1) VE0))).tyvars,
        ∀ b ∈ ((th st1).img c).vars, ∃ c' ∈ C.tyvars, b ∈ ((th st1).img c').vars := by
      intro c hc b hb
      rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
      · exact ⟨c, hc, hb⟩
      · have hA := (hVEc q hq).2.2 c hcq
        rw [hp.A_fixed hθ1 hi1.idem hA, vars_vty, List.mem_singleton] at hb; subst hb
        exact hp.A_src hθ1 hA
    have hR : ∀ b, Reach (th st1) (C.plusVE (closGroup (ctxRsb (th st1) C).tyvars (rsbVE (th st1) VE0))) st1.n b →
        Reach (th st) C st.n b := by
      rintro b (hb | ⟨c, hc, hb⟩)
      · exact .inl (new_of_new PD.seg.le hb)
      · obtain ⟨c', hc', hb'⟩ := hsrc c hc b hb
        exact reach_shrink PD.seg hp.inv hc' hb'
    have hAv : AvoidK (((ctxRsb (th st1) C).tyvars, veBodies (rsbVE (th st1) VE0)) :: Kd)
        (Reach (th st1) (C.plusVE (closGroup (ctxRsb (th st1) C).tyvars (rsbVE (th st1) VE0))) st1.n) := by
      rintro k hk b hg (hb | ⟨c, hc, hb⟩)
      · rw [(PDk.ks.zone k hk b hg).2] at hb; cases hb
      · obtain ⟨c', hc', hb'⟩ := hsrc c hc b hb
        exact PDk.ks.old k hk b hg c' (hp.old hc') hb'
    have P := PDk.seq PB hR hAv
    refine ⟨_, P.weaken (covSub fun τ hτ => by simpa using hτ) fun s hs ⟨⟨⟨cD, hab⟩, hdk⟩, cB⟩ U hU hcn ⟨wD, wE⟩ => ?_⟩
    have H : ClosHypD n0 C VE0 (th st1) s :=
      { isMono := fun q hq => (hmono q hq).1
        ok := fun q hq v hv => (PD.okT _ (List.mem_map.mpr ⟨q, hq, rfl⟩) v hv).1
        θok := hθ1
        idem := hi1.idem
        sok := hs
        abs := hab
        dead := hdk
        ctxB := hp.ctxB
        ctxF := hp.ctxF
        rest := hp.rest }
    simp only [tysAtExp] at hcn
    have cD' := cD U hU (hcn.sub fun τ hτ => List.mem_append_left _ hτ) wD
    obtain ⟨cB', tB⟩ := cB U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) wE
    simp only at cD' cB' tB
    rw [ctxRsb_plusVE, closGroup_rsb H] at cB'
    refine ⟨?_, ?_⟩
    · simp only [rsbAtExp, checkAtExp, Bool.and_eq_true]
      refine ⟨cD', ?_⟩
      simp only [rsbDec, ADec.result]
      exact cB'
    · simp only [rsbAtExp, AAtExp.ty]; exact tB
  | .paren e, C, st, r, st', hp, h => by
    simp only [wdAtExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD k1
    exact ⟨_, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkAtExp, rsbAtExp, AAtExp.ty] using c U hU hcn hw⟩
theorem wdExpRow_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (row : BExpRow) (C : Ctx) (st : WDSt) (r : Row × AExpRow) (st' : WDSt),
    SPre n0 L C st → wdExpRow fuel (rigidFromD n0) C row st = .ok r st' →
    Post n0 C st st' (r.1.map (·.2)) (fun s => XCk n0 s (tysExpRow false r.2) (fun U => CWExpRow L U r.2)
      (checkExpRow (ctxRsb s C) (rsbExpRow s r.2) = true ∧ (rsbExpRow s r.2).row = rsbRow s r.1)) ∧ Sorted r.1
  | .field l e rest, C, st, r, st', hp, h => by
    simp only [wdExpRow] at h
    obtain ⟨⟨τ, ae⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨ρ, ar⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e C st _ st1 hp h1
    obtain ⟨⟨K2, P2⟩, hs2⟩ := wdExpRowOpt_sound fuel n0 hL rest C st1 _ st2 (hp.later P1.seg) h2
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    have P12 := PostK.seqSame hp P1 P2
    refine ⟨⟨_, P12.weaken ?_ fun s _ ⟨c1, c2⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩, sorted_modify_single hs2⟩
    · intro x hx v hv
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
      rcases mem_modify1 hp' with rfl | hp'
      · exact ⟨_, by simp, hv⟩
      · exact ⟨p.2, List.mem_append_right _ (List.mem_map_of_mem hp'), hv⟩
    · simp only [tysExpRow] at hcn
      obtain ⟨c1, t1⟩ := c1 U hU (hcn.sub fun τ hτ => List.mem_append_left _ hτ) w1
      obtain ⟨c2, t2⟩ := c2 U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) w2
      simp only at c1 t1 c2 t2
      refine ⟨by simp only [checkExpRow, rsbExpRow, c1, c2, Bool.and_self], ?_⟩
      simp only [rsbExpRow, AExpRow.row, t1, t2, rowOpt_ty_modify]
theorem wdExpRowOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (row : Option BExpRow) (C : Ctx) (st : WDSt) (r : Row × Option AExpRow) (st' : WDSt),
    SPre n0 L C st → wdExpRowOpt fuel (rigidFromD n0) C row st = .ok r st' →
    Post n0 C st st' (r.1.map (·.2)) (fun s => XCk n0 s (tysExpRowOpt false r.2) (fun U => CWExpRowOpt L U r.2)
      (checkExpRowOpt (ctxRsb s C) (rsbExpRowOpt s r.2) = true ∧ AExpRow.rowOpt (rsbExpRowOpt s r.2) = rsbRow s r.1)) ∧
      Sorted r.1
  | none, C, st, r, st', hp, h => by
    simp only [wdExpRowOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨⟨[], (PostK.start hp).weaken (covSub fun τ hτ => by simp at hτ) fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩, sorted_nil⟩
  | some row, C, st, r, st', hp, h => by
    simp only [wdExpRowOpt] at h
    obtain ⟨⟨ρ, a⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨K1, P1⟩, hs1⟩ := wdExpRow_sound fuel n0 hL row C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD k1
    exact ⟨⟨_, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkExpRowOpt, rsbExpRowOpt, AExpRow.rowOpt] using c U hU hcn hw⟩, hs1⟩
theorem wdExp_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (e : BExp) (C : Ctx) (st : WDSt) (r : Ty × AExp) (st' : WDSt),
    SPre n0 L C st → wdExp fuel (rigidFromD n0) C e st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => XCk n0 s (tysExp false r.2) (fun U => CWExp L U r.2)
      (checkExpS (ctxRsb s C) (rsbExp s r.2) = true ∧ (rsbExp s r.2).ty = rsb s r.1))
  | .atexp a, C, st, r, st', hp, h => by
    simp only [wdExp] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wdAtExp_sound fuel n0 hL a C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD k1
    exact ⟨_, P1.weaken (cov_refl _) fun s _ c U hU hcn hw => by
      simpa [checkExpS, rsbExp, AExp.ty] using c U hU hcn hw⟩
  | .app e a, C, st, r, st', hp, h => by
    simp only [wdExp] at h
    obtain ⟨⟨τ1, ae⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨τ2, aa⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨β, st3, h3, k3⟩ := wdbind_ok k2
    obtain ⟨rfl, rfl⟩ := freshVD_ok h3
    obtain ⟨_, st4, h4, k4⟩ := wdbind_ok k3
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wdAtExp_sound fuel n0 hL a C st1 _ st2 (hp.later P1.seg) h2
    have P3 := (PostK.seqSame hp P1 P2).fresh
    have hi2 := (PostK.seqSame hp P1 P2).seg.inv
    have P4 := P3.unify (τ1 := τ1) (τ2 := .fn τ2 (.var (.fresh st2.n .any)))
      (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · simp only [Ty.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact ⟨τ2, by simp, hv⟩
          · exact ⟨.var (.fresh st2.n .any), by simp, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_okD k4
    refine ⟨_, P4.weaken (covSub fun τ hτ => by simp at hτ; simp [hτ]) fun s hs ⟨⟨c1, c2⟩, hab3, he⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩
    simp only [tysExp] at hcn
    have hcn1 : CnL U (tysExp false ae) := hcn.sub fun τ hτ => List.mem_append_left _ hτ
    have hcn2 : CnL U (tysAtExp false aa) := hcn.sub fun τ hτ => List.mem_append_right _ hτ
    obtain ⟨c1, t1⟩ := c1 U hU hcn1 w1
    obtain ⟨c2, t2⟩ := c2 U hU hcn2 w2
    simp only at c1 t1 c2 t2
    have eq := he (cn_th hab3 (by rw [← t1]; exact cnS_exp hs hU hcn1)) (by
      simp only [rsb, cnB, Bool.and_eq_true]
      exact ⟨cn_th hab3 (by rw [← t2]; exact cnS_atexp hs hU hcn2), cn_fresh_th hi2 (Nat.le_refl _)⟩)
    have hty : (rsbExp s ae).ty = .fn (rsbAtExp s aa).ty (rsb s (.var (.fresh st2.n .any))) := by
      rw [t1, eq, t2]; rfl
    simp only [checkExpS, rsbExp, c1, c2, Bool.true_and, hty, decide_true, AExp.ty, Ty.cod, and_self]
  | .lam p e, C, st, r, st', hp, h => by
    simp only [wdExp] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨e1, P1⟩ := wdAtPat_sound fuel n0 hL p C st _ st1 hp h1
    simp only at e1; subst e1
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
      ⟨(atpat_ve ap q hq).1, (atpat_ve ap q hq).2.1, (atpat_ve ap q hq).2.2⟩
    obtain ⟨K2, P2⟩ := wdExp_sound fuel n0 hL e _ st1 _ st2 hpB h2
    have P12 := P1.seq P2 hR hA
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    refine ⟨_, P12.weaken (cov_fnD (fun v hv => by
        obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩)
      (fun v hv => ⟨τe, by simp, hv⟩)) fun s _ ⟨cp, ce⟩ U hU hcn ⟨wp, we⟩ => ?_⟩
    simp only [tysExp] at hcn
    have cp' := cp U hU (hcn.sub fun τ hτ => List.mem_append_left _ hτ) wp
    obtain ⟨ce', te⟩ := ce U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) we
    simp only at ce' te
    rw [ctxRsb_plusVE] at ce'
    simp only [checkExpS, rsbExp, cp', rsbAtPat_veD, ce', Bool.and_self, AExp.ty, rsbAtPat_tyD, te, rsb, true_and]
  | .caseE e m, C, st, r, st', hp, h => by
    simp only [wdExp] at h
    obtain ⟨⟨τe, ae⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨τm, am⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨β, st3, h3, k3⟩ := wdbind_ok k2
    obtain ⟨rfl, rfl⟩ := freshVD_ok h3
    obtain ⟨_, st4, h4, k4⟩ := wdbind_ok k3
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wdMatch_sound fuel n0 hL m C st1 _ st2 (hp.later P1.seg) h2
    have P3 := (PostK.seqSame hp P1 P2).fresh
    have hi2 := (PostK.seqSame hp P1 P2).seg.inv
    have P4 := P3.unify (τ1 := τm) (τ2 := .fn τe (.var (.fresh st2.n .any)))
      (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · simp only [Ty.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact ⟨τe, by simp, hv⟩
          · exact ⟨.var (.fresh st2.n .any), by simp, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_okD k4
    refine ⟨_, P4.weaken (covSub fun τ hτ => by simp at hτ; simp [hτ]) fun s hs ⟨⟨c1, c2⟩, hab3, he⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩
    simp only [tysExp] at hcn
    have hcn1 : CnL U (tysExp false ae) := hcn.sub fun τ hτ => List.mem_append_left _ hτ
    have hcn2 : CnL U (tysMatch false am) := hcn.sub fun τ hτ => List.mem_append_right _ hτ
    obtain ⟨c1, t1⟩ := c1 U hU hcn1 w1
    obtain ⟨c2, t2⟩ := c2 U hU hcn2 w2
    simp only at c1 t1 c2 t2
    have eq := he (cn_th hab3 (by rw [← t2]; exact cnS_match hs hU hcn2)) (by
      simp only [rsb, cnB, Bool.and_eq_true]
      exact ⟨cn_th hab3 (by rw [← t1]; exact cnS_exp hs hU hcn1), cn_fresh_th hi2 (Nat.le_refl _)⟩)
    have hty : (rsbMatch s am).ty = .fn (rsbExp s ae).ty (rsb s (.var (.fresh st2.n .any))) := by
      rw [t2, eq, t1]; rfl
    simp only [checkExpS, rsbExp, c1, c2, Bool.true_and, hty, decide_true, AExp.ty, Ty.cod, and_self]
theorem wdExpOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (e : Option BExp) (C : Ctx) (st : WDSt) (r : Option Ty × Option AExp) (st' : WDSt),
    SPre n0 L C st → wdExpOpt fuel (rigidFromD n0) C e st = .ok r st' →
    Post n0 C st st' r.1.toList (fun s => XCk n0 s (tysExpOpt false r.2) (fun U => CWExpOpt L U r.2)
      (checkExpOpt (ctxRsb s C) (rsbExpOpt s r.2) = true ∧ AExp.tyOpt (rsbExpOpt s r.2) = rsbOpt s r.1))
  | none, C, st, r, st', hp, h => by
    simp only [wdExpOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨[], (PostK.start hp).weaken (covSub fun τ hτ => by simp at hτ) fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩
  | some e, C, st, r, st', hp, h => by
    simp only [wdExpOpt] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_okD k1
    exact ⟨_, P1.weaken (covSub fun τ hτ => by simpa using hτ) fun s _ c U hU hcn hw => by
      simpa [checkExpOpt, rsbExpOpt, AExp.tyOpt, rsbOpt] using c U hU hcn hw⟩
theorem wdMatch_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (m : BMatch) (C : Ctx) (st : WDSt) (r : Ty × AMatch) (st' : WDSt),
    SPre n0 L C st → wdMatch fuel (rigidFromD n0) C m st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => XCk n0 s (tysMatch false r.2) (fun U => CWMatch L U r.2)
      (checkMatch (ctxRsb s C) (rsbMatch s r.2) = true ∧ (rsbMatch s r.2).ty = rsb s r.1))
  | .mk mr rest, C, st, r, st', hp, h => by
    simp only [wdMatch] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨ar, st2, h2, k2⟩ := wdbind_ok k1
    obtain ⟨K1, P1⟩ := wdMRule_sound fuel n0 hL mr C st _ st1 hp h1
    obtain ⟨K2, P2⟩ := wdMatchOpt_sound fuel n0 hL rest C τ1 st1 ar st2 st [τ1] _ K1 hp P1 (by simp) h2
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    refine ⟨_, P2.weaken (cov_refl _) fun s hs ⟨c1, c2⟩ U hU hcn ⟨w1, w2⟩ => ?_⟩
    simp only [tysMatch] at hcn
    have hcn1 : CnL U (tysMRule false a1) := hcn.sub fun τ hτ => List.mem_append_left _ hτ
    obtain ⟨c1, t1⟩ := c1 U hU hcn1 w1
    simp only at c1 t1
    have c2' := c2 U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) w2 (by rw [← t1]; exact cnS_mrule hs hU hcn1)
    simp only [checkMatch, rsbMatch, c1, Bool.true_and, AMatch.ty, and_true]
    rw [t1]; exact ⟨c2', rfl⟩
theorem wdMatchOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (m : Option BMatch) (C : Ctx) (τ : Ty) (st1 : WDSt) (r : Option AMatch)
    (st2 : WDSt) (st0 : WDSt) (tys : List Ty) (Chk : RSub → Prop) (K : List ConW),
    SPre n0 L C st0 → PostK n0 C st0 st1 tys Chk K → τ ∈ tys →
    wdMatchOpt fuel (rigidFromD n0) C τ m st1 = .ok r st2 →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ XCk n0 s (tysMatchOpt false r) (fun U => CWMatchOpt L U r)
      (cnB (rsb s τ) = true → checkMatchOptAt (ctxRsb s C) (rsb s τ) (rsbMatchOpt s r) = true))
  | none, C, τ, st1, r, st2, st0, tys, Chk, K, hp, P0, hτ, h => by
    simp only [wdMatchOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨K, P0.weaken (cov_refl _) fun s _ c => ⟨c, fun _ _ _ _ _ => rfl⟩⟩
  | some m, C, τ, st1, r, st2, st0, tys, Chk, K, hp, P0, hτ, h => by
    simp only [wdMatchOpt] at h
    obtain ⟨⟨τm, am⟩, st3, h3, k3⟩ := wdbind_ok h; dsimp only at k3
    obtain ⟨_, st4, h4, k4⟩ := wdbind_ok k3
    obtain ⟨K1, P1⟩ := wdMatch_sound fuel n0 hL m C st1 _ st3 (hp.later P0.seg) h3
    have P01 := PostK.seqSame hp P0 P1
    have P2 := P01.unify (τ1 := τm) (τ2 := τ) (fun x hx v hv => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨x, by simp, hv⟩
      · exact ⟨x, List.mem_append_left _ hτ, hv⟩) h4
    obtain ⟨rfl, rfl⟩ := pure_okD k4
    refine ⟨_, P2.weaken (covSub fun τ' hτ' => List.mem_append_left _ hτ') fun s hs ⟨⟨c0, c1⟩, hab, he⟩ =>
      ⟨c0, fun U hU hcn hw hcτ => ?_⟩⟩
    simp only [tysMatchOpt] at hcn
    obtain ⟨c1, t1⟩ := c1 U hU hcn hw
    simp only at c1 t1
    have eq := he (cn_th hab (by rw [← t1]; exact cnS_match hs hU hcn)) (cn_th hab hcτ)
    simp only [checkMatchOptAt, rsbMatchOpt, c1, Bool.true_and, decide_eq_true_eq, t1, eq]
theorem wdMRule_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (mr : BMRule) (C : Ctx) (st : WDSt) (r : Ty × AMRule) (st' : WDSt),
    SPre n0 L C st → wdMRule fuel (rigidFromD n0) C mr st = .ok r st' →
    Post n0 C st st' [r.1] (fun s => XCk n0 s (tysMRule false r.2) (fun U => CWMRule L U r.2)
      (checkMRule (ctxRsb s C) (rsbMRule s r.2) = true ∧ (rsbMRule s r.2).ty = rsb s r.1))
  | .mk p e, C, st, r, st', hp, h => by
    simp only [wdMRule] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
    obtain ⟨e1, P1⟩ := wdPat_sound fuel n0 hL p C st _ st1 hp h1
    simp only at e1; subst e1
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
      ⟨(pat_ve ap q hq).1, (pat_ve ap q hq).2.1, (pat_ve ap q hq).2.2⟩
    obtain ⟨K2, P2⟩ := wdExp_sound fuel n0 hL e _ st1 _ st2 hpB h2
    have P12 := P1.seq P2 hR hA
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    refine ⟨_, P12.weaken (cov_fnD (fun v hv => by
        obtain ⟨τ', h1', h2'⟩ := pat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩)
      (fun v hv => ⟨τe, by simp, hv⟩)) fun s _ ⟨cp, ce⟩ U hU hcn ⟨wp, we⟩ => ?_⟩
    simp only [tysMRule] at hcn
    have cp' := cp U hU (hcn.sub fun τ hτ => List.mem_append_left _ hτ) wp
    obtain ⟨ce', te⟩ := ce U hU (hcn.sub fun τ hτ => List.mem_append_right _ hτ) we
    simp only at ce' te
    rw [ctxRsb_plusVE] at ce'
    simp only [checkMRule, rsbMRule, cp', rsbPat_veD, ce', Bool.and_self, AMRule.ty, rsbPat_tyD, te, rsb, true_and]
theorem wdDec_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (d : BDec) (C : Ctx) (st : WDSt) (r : ADec) (st' : WDSt),
    SPre n0 L C st → wdDec fuel (rigidFromD n0) C d st = .ok r st' →
    Post n0 C st st' (veBodies r.env) (fun s => XCk n0 s (tysDec false r) (fun U => CWDec L U r)
      (checkDec (ctxRsb s C) (rsbDec s r) = true)) ∧ ∀ q ∈ r.env, q.2.1.bound = [] ∧ q.2.2 = .v
  | .val (.pat p e), C, st, r, st', hp, h => by
    simp only [wdDec] at h
    obtain ⟨⟨τp, ap⟩, st1, h1, k1⟩ := wdbind_ok h; dsimp only at k1
    by_cases hsh : (ap.ve.all fun q => !conBound C q.1) = true
    · rw [if_pos hsh] at k1
      obtain ⟨⟨τe, ae⟩, st2, h2, k2⟩ := wdbind_ok k1; dsimp only at k2
      obtain ⟨_, st3, h3, k3⟩ := wdbind_ok k2
      obtain ⟨e1, P1⟩ := wdAtPat_sound fuel n0 hL p C st _ st1 hp h1
      simp only at e1; subst e1
      obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := ap.ve) hp P1 fun q hq =>
        ⟨(atpat_ve ap q hq).1, (atpat_ve ap q hq).2.1, (atpat_ve ap q hq).2.2⟩
      obtain ⟨K2, P2⟩ := wdExp_sound fuel n0 hL e _ st1 _ st2 hpB h2
      have P3 := (P1.seq P2 hR hA).unify (τ1 := τe) (τ2 := ap.ty) (fun x hx v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, hv⟩
        · obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars ap v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩) h3
      obtain ⟨rfl, rfl⟩ := pure_okD k3
      refine ⟨⟨_, P3.weaken ?_ fun s hs ⟨⟨cp, ce⟩, hab, he⟩ U hU hcn hw => ?_⟩, fun q hq =>
        ⟨(atpat_ve ap q hq).1, (atpat_ve ap q hq).2.1⟩⟩
      · intro x hx v hv
        simp only [ADec.env, veBodies, List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        obtain ⟨τ', h1', h2'⟩ := (atpat_ve ap q hq).2.2 v hv
        exact ⟨τ', List.mem_append_left _ h1', h2'⟩
      · simp only [tysDec, tysValBind, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hcn
        simp only [CWDec, CWValBind] at hw
        have hcnp : CnL U (tysAtPat ap) := hcn.sub fun τ hτ => List.mem_append_left _ hτ
        have hcne : CnL U (tysExp false ae) := hcn.sub fun τ hτ => List.mem_append_right _ hτ
        have cp' := cp U hU hcnp hw.1
        obtain ⟨ce', te⟩ := ce U hU hcne hw.2
        simp only at ce' te
        rw [ctxRsb_plusVE] at ce'
        have eq := he (cn_th hab (by rw [← te]; exact cnS_exp hs hU hcne))
          (cn_th hab (hU.cn (cnU_atpat (fix_bnd0D hU.1) hcnp)))
        simp only [ADec.env, checkDec, rsbDec]
        rw [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨?_, by simp [rsbValBind, AValBind.ve, rsbAtPat_veD]⟩
        simp only [rsbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨checkAtPat_lkC (lkC_noShadowD hsh) _ cp', ce'⟩, by rw [te, eq, rsbAtPat_tyD]⟩
    · rw [if_neg hsh] at k1; cases k1
  | .val (.var x ann e rest), C, st, r, st', hp, h => by
    simp only [wdDec] at h
    obtain ⟨es, st1, h1, k1⟩ := wdbind_ok h
    obtain ⟨avb, st2, h2, k2⟩ := wdbind_ok k1
    obtain ⟨hes, PG⟩ := groupEntriesD_sound _ st es st1 hp h1
    have hmono := groupVE_mono (.var x ann e rest) es (fun e he => (hes e he).1)
    obtain ⟨⟨K2, PM⟩, hve, hann⟩ := wdMembers_sound fuel n0 hL (.var x ann e rest) _ es st1 avb st2 C
      (groupVE (.var x ann e rest) es) st (es.map (·.2)) _ _ h2 rfl hp PG
      (fun q hq => ⟨(hmono q hq).1, (hmono q hq).2.1, by
        obtain ⟨-, -, e', he', hb⟩ := hmono q hq; rw [hb]; exact List.mem_map_of_mem he'⟩)
      (fun e' he' => ⟨List.mem_map_of_mem he', (hes e' he').1, (hes e' he').2⟩)
    obtain ⟨rfl, rfl⟩ := pure_okD k2
    refine ⟨⟨K2, PM.weaken ?_ fun s _ ⟨_, cv⟩ U hU hcn hw => ?_⟩, fun q hq => ⟨(hmono q hq).1, (hmono q hq).2.1⟩⟩
    · intro x' hx v hv
      simp only [ADec.env, veBodies, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨-, -, e', he', hb⟩ := hmono q hq
      exact ⟨e'.2, List.mem_map_of_mem he', by rw [← hb]; exact hv⟩
    · simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hcn
      simp only [CWDec] at hw
      simp only [checkDec, rsbDec, Bool.and_eq_true, decide_eq_true_eq]
      rw [← ctxRsb_plusVE]
      exact ⟨cv U hU hcn hw, by rw [valbind_ve_sbD s avb hann, hve]⟩
theorem wdMembers_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (vb : BValBind) (Cg : Ctx) (es : List (Option (BTy × List BVar) × Ty))
    (st1 : WDSt) (avb : AValBind) (st2 : WDSt) (C : Ctx) (VE0 : ValEnv) (st0 : WDSt) (tys : List Ty)
    (Chk : RSub → Prop) (K : List ConW),
    wdMembers fuel (rigidFromD n0) Cg vb es st1 = .ok avb st2 → Cg = C.plusVE VE0 → SPre n0 L C st0 →
    PostK n0 C st0 st1 tys Chk K → (∀ q ∈ VE0, q.2.1.bound = [] ∧ q.2.2 = .v ∧ q.2.1.body ∈ tys) →
    (∀ e ∈ es, e.2 ∈ tys ∧ annU e.1 = [] ∧ ∀ (C' : Ctx) (s : RSub), C'.U = C.U →
      (∀ lc, C'.lookupTy lc = C.lookupTy lc) → checkAnn C' e.1 (rsb s e.2) = true) →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ XCk n0 s (tysValBind false avb) (fun U => CWValBind L U avb)
      (checkValBind (ctxRsb s Cg) (rsbValBind s avb) = true)) ∧
      avb.ve = groupVE vb es ∧ AnnNilV avb
  | .var x _ e rest, Cg, (ann, τx) :: es, st1, avb, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    subst hCg
    simp only [wdMembers] at h
    obtain ⟨⟨τe, ae⟩, st3, h3, k3⟩ := wdbind_ok h; dsimp only at k3
    obtain ⟨_, st4, h4, k4⟩ := wdbind_ok k3
    obtain ⟨ar, st5, h5, k5⟩ := wdbind_ok k4
    obtain ⟨hτx, hann, hck⟩ := hes _ (.head _)
    rw [hann, plusU_nil] at h3
    obtain ⟨hpB, hR, hA⟩ := PostK.plusVE_pre (VE := VE0) hp P0 fun q hq =>
      ⟨(hVE q hq).1, (hVE q hq).2.1, fun v hv => ⟨_, (hVE q hq).2.2, hv⟩⟩
    obtain ⟨K1, P1⟩ := wdExp_sound fuel n0 hL e _ st1 _ st3 hpB h3
    have P2 := (P0.seq P1 hR hA).unify (τ1 := τe) (τ2 := τx) (fun x' hx v hv => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨x', by simp, hv⟩
      · exact ⟨x', List.mem_append_left _ hτx, hv⟩) h4
    have P2' := P2.weaken (covSub fun τ' hτ' => List.mem_append_left _ hτ') fun _ _ c => c
    obtain ⟨⟨K3, P3⟩, hst⟩ := wdMembersOpt_sound fuel n0 hL rest _ es st4 ar st5 C VE0 st0 tys _ _ h5 rfl hp P2' hVE
      (fun e' he' => hes e' (.tail _ he'))
    obtain ⟨rfl, rfl⟩ := pure_okD k5
    refine ⟨⟨K3, P3.weaken (cov_refl _) fun s hs ⟨⟨⟨c0, ce⟩, hab, he⟩, cr⟩ => ⟨c0, fun U hU hcn hw => ?_⟩⟩, ?_, ?_⟩
    · simp only [tysValBind, annMark, List.nil_append, List.cons_append] at hcn
      simp only [CWValBind] at hw
      have hcne : CnL U (tysExp false ae) := hcn.sub fun τ hτ => by simp [hτ]
      obtain ⟨ce', te⟩ := ce U hU hcne hw.1
      have cr' := cr U hU (hcn.sub fun τ hτ => by simp [hτ]) hw.2
      simp only at ce' te cr'
      have eq := he (cn_th hab (by rw [← te]; exact cnS_exp hs hU hcne))
        (cn_th hab (hU.cn (hcn _ (List.mem_cons_self ..))))
      simp only [checkValBind, rsbValBind, Bool.and_eq_true, decide_eq_true_eq, hann, plusU_nil, ce', cr', and_true,
        true_and]
      refine ⟨hck _ s rfl (fun lc => rfl), ?_⟩
      rw [te, eq]
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
    simp only [wdMembers] at h; cases h
  | .pat _ _, Cg, es, st1, avb, st2, C, VE0, st0, tys, Chk, K, h, _, _, _, _, _ => by
    simp only [wdMembers] at h; cases h
theorem wdMembersOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} (hL : LOk n0 L) :
    ∀ (vb : Option BValBind) (Cg : Ctx)
    (es : List (Option (BTy × List BVar) × Ty)) (st1 : WDSt) (r : Option AValBind) (st2 : WDSt) (C : Ctx)
    (VE0 : ValEnv) (st0 : WDSt) (tys : List Ty) (Chk : RSub → Prop) (K : List ConW),
    wdMembersOpt fuel (rigidFromD n0) Cg vb es st1 = .ok r st2 → Cg = C.plusVE VE0 → SPre n0 L C st0 →
    PostK n0 C st0 st1 tys Chk K → (∀ q ∈ VE0, q.2.1.bound = [] ∧ q.2.2 = .v ∧ q.2.1.body ∈ tys) →
    (∀ e ∈ es, e.2 ∈ tys ∧ annU e.1 = [] ∧ ∀ (C' : Ctx) (s : RSub), C'.U = C.U →
      (∀ lc, C'.lookupTy lc = C.lookupTy lc) → checkAnn C' e.1 (rsb s e.2) = true) →
    Post n0 C st0 st2 tys (fun s => Chk s ∧ XCk n0 s (tysValBindOpt false r) (fun U => CWValBindOpt L U r)
      (checkValBindOpt (ctxRsb s Cg) (rsbValBindOpt s r) = true)) ∧
      (match vb, r with
       | none, none => True
       | some vb, some avb => avb.ve = groupVE vb es ∧ AnnNilV avb
       | _, _ => False)
  | none, Cg, es, st1, r, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    simp only [wdMembersOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact ⟨⟨K, P0.weaken (cov_refl _) fun s _ c => ⟨c, fun _ _ _ _ => rfl⟩⟩, trivial⟩
  | some vb, Cg, es, st1, r, st2, C, VE0, st0, tys, Chk, K, h, hCg, hp, P0, hVE, hes => by
    simp only [wdMembersOpt] at h
    obtain ⟨a, st3, h3, k3⟩ := wdbind_ok h
    obtain ⟨⟨K1, P1⟩, hve, hann⟩ := wdMembers_sound fuel n0 hL vb Cg es st1 a st3 C VE0 st0 tys Chk K h3 hCg hp P0 hVE hes
    obtain ⟨rfl, rfl⟩ := pure_okD k3
    exact ⟨⟨K1, P1.weaken (cov_refl _) fun s _ ⟨c0, c⟩ => ⟨c0, fun U hU hcn hw => by
      simpa [checkValBindOpt, rsbValBindOpt] using c U hU hcn hw⟩⟩, hve, hann⟩
end

end WDS

end StandardElm.Stat.Complete
