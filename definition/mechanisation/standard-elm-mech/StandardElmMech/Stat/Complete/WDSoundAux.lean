/-
  A Standard Definition of Elm? Mechanisation: lemmas for the expression cases of L10 with rows
  (plan step 11, milestone (d); WSoundAux.lean for `inferExpWD`): constructor witnesses through
  expressions, contexts under substitution, the free variables of `θ C` at a closure and the
  constraint a closure records (`kseg_closD`), group entries, pattern bindings that shadow no
  constructor.
-/
import StandardElmMech.Stat.Complete.WDSoundPats

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

namespace WDS

/-! ## Constructor witnesses through expressions -/

mutual
def CWAtExp (L : LongId → Option Scheme) (U : RSub) : AAtExp → Prop
  | .tuple e1 e2 e3 => CWExp L U e1 ∧ CWExp L U e2 ∧ CWExpOpt L U e3
  | .record r => CWExpRowOpt L U r
  | .update _ _ _ r => CWExpRow L U r
  | .letE d e => CWDec L U d ∧ CWExp L U e
  | .paren e => CWExp L U e
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .unit | .nil _ => True
def CWExpRow (L : LongId → Option Scheme) (U : RSub) : AExpRow → Prop
  | .field _ e rest => CWExp L U e ∧ CWExpRowOpt L U rest
def CWExpRowOpt (L : LongId → Option Scheme) (U : RSub) : Option AExpRow → Prop
  | none => True
  | some r => CWExpRow L U r
def CWExp (L : LongId → Option Scheme) (U : RSub) : AExp → Prop
  | .atexp a => CWAtExp L U a
  | .app e a => CWExp L U e ∧ CWAtExp L U a
  | .lam p e => CWAtPat L U p ∧ CWExp L U e
  | .caseE e m => CWExp L U e ∧ CWMatch L U m
def CWExpOpt (L : LongId → Option Scheme) (U : RSub) : Option AExp → Prop
  | none => True
  | some e => CWExp L U e
def CWMatch (L : LongId → Option Scheme) (U : RSub) : AMatch → Prop
  | .mk mr rest => CWMRule L U mr ∧ CWMatchOpt L U rest
def CWMatchOpt (L : LongId → Option Scheme) (U : RSub) : Option AMatch → Prop
  | none => True
  | some m => CWMatch L U m
def CWMRule (L : LongId → Option Scheme) (U : RSub) : AMRule → Prop
  | .mk p e => CWPat L U p ∧ CWExp L U e
def CWDec (L : LongId → Option Scheme) (U : RSub) : ADec → Prop
  | .val _ vb => CWValBind L U vb
def CWValBind (L : LongId → Option Scheme) (U : RSub) : AValBind → Prop
  | .var _ _ _ e rest => CWExp L U e ∧ CWValBindOpt L U rest
  | .pat p e => CWAtPat L U p ∧ CWExp L U e
def CWValBindOpt (L : LongId → Option Scheme) (U : RSub) : Option AValBind → Prop
  | none => True
  | some vb => CWValBind L U vb
end

/-! ## Contexts under substitution -/

theorem ctxRsb_plusVE (s : RSub) (C : Ctx) (VE : ValEnv) :
    ctxRsb s (C.plusVE VE) = (ctxRsb s C).plusVE (rsbVE s VE) := by
  simp [ctxRsb, Ctx.plusVE, rsbVE]

theorem ctxRsb_plusU (s : RSub) (C : Ctx) (U' : List BVar) : ctxRsb s (C.plusU U') = (ctxRsb s C).plusU U' := rfl

theorem lookupVal_ctxRsb_c {s : RSub} {C : Ctx} {lv : LongId} {σ : Scheme}
    (h : (ctxRsb s C).lookupVal lv = some (σ, .c)) : ∃ σ0, C.lookupVal lv = some (σ0, .c) := by
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at h ⊢
    change FMap.find? (rsbVE s C.E.VE) lv.id = _ at h
    rw [find?_rsbVE] at h
    cases hf : FMap.find? C.E.VE lv.id with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p.1, by rw [← h.2]⟩
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at h ⊢
    exact ⟨σ, h⟩

theorem lkC_noShadowD {s : RSub} {C : Ctx} {VE : ValEnv} (h : (VE.all fun q => !conBound C q.1) = true) :
    LkC (ctxRsb s C) ((ctxRsb s C).plusVE (rsbVE s VE)) := by
  intro lv σ hl
  rw [lookupVal_plusVE]
  cases hq : lv.qual with
  | none =>
    simp only
    cases hf : FMap.find? (rsbVE s VE) lv.id with
    | none => simp only [Option.none_or]; simpa [Ctx.lookupVal, Env.lookupVal, hq] using hl
    | some p =>
      exfalso
      rw [find?_rsbVE] at hf
      cases hf' : FMap.find? VE lv.id with
      | none => rw [hf'] at hf; cases hf
      | some p0 =>
        have hm := find?_mem hf'
        have := List.all_eq_true.mp h _ hm
        obtain ⟨σ0, hl0⟩ := lookupVal_ctxRsb_c hl
        have hl1 : C.lookupVal ⟨none, lv.id⟩ = some (σ0, .c) := by
          rw [← hl0]; cases lv; simp_all
        simp [conBound, hl1] at this
  | some m => simpa using hl

theorem valbind_ve_sbD (T : RSub) : ∀ vb : AValBind, AnnNilV vb → (rsbValBind T vb).ve = rsbVE T vb.ve
  | .var x ann τ e rest, h => by
    unfold AnnNilV at h
    simp only [rsbValBind]
    unfold AValBind.ve
    rw [rsbVE_modifyD]
    congr 1
    · simp [h.1, annScheme_nil, rsbVE, rsbScheme, mono]
    · cases rest with
      | none => rfl
      | some vb => exact valbind_ve_sbD T vb h.2
  | .pat p e, _ => by simp only [rsbValBind, AValBind.ve, rsbAtPat_veD]

/-! ## The free variables of `θ C` -/

section
variable {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (hp : SPre n0 L C st)
include hp

theorem SPre.A_src {θ : RSub} (hθ : SOk n0 θ) {c : BVar} (h : c ∈ (ctxRsb θ C).tyvars) :
    ∃ c' ∈ C.tyvars, c ∈ (θ.img c').vars := by
  rcases ctxRsb_tyvars_mem (fun v hv => hθ.bnd hv) hp.ctxB h with hr | ⟨x, p, e, hf, he, hnb, hce⟩
  · refine ⟨c, mem_ctx_tyvars.mpr (.inl hr), ?_⟩
    rw [hθ.fix c (hp.rest c hr), vars_vty]; exact List.mem_singleton_self _
  · exact ⟨e, mem_ctx_tyvars.mpr (.inr ⟨x, p, hf, mem_scheme_tyvars.mpr ⟨he, hp.ctxF x p hf e he hnb, hnb⟩⟩), hce⟩

theorem SPre.A_fixed {θ : RSub} (hθ : SOk n0 θ) (hi : IdemS θ) {c : BVar} (h : c ∈ (ctxRsb θ C).tyvars) :
    θ.img c = vty c := by
  obtain ⟨c', _, hc⟩ := hp.A_src hθ h
  exact hi c' c hc

theorem SPre.inA {θ : RSub} (hθ : SOk n0 θ) {c b : BVar} (hc : c ∈ C.tyvars) (hb : b ∈ (θ.img c).vars) :
    b ∈ (ctxRsb θ C).tyvars := by
  rcases mem_ctx_tyvars.mp hc with hr | ⟨x, p, hf, hcp⟩
  · rw [hθ.fix c (hp.rest c hr), vars_vty, List.mem_singleton] at hb; subst hb
    exact mem_ctx_tyvars.mpr (.inl hr)
  · obtain ⟨hc1, hc2, -⟩ := mem_scheme_tyvars.mp hcp
    exact ctxRsb_tyvars_of hp.ctxB (hθ.img c hc2 b hb) hf hc1 hb

end

/-- The free variables of a member's closure: free in the context. -/
theorem closE_tyvarsD {A : List BVar} {VE : ValEnv} {τ : Ty} {v : BVar}
    (h : v ∈ (closE A VE (mono τ)).tyvars) : v ∈ τ.vars ∧ v ∈ A := by
  unfold closE at h
  rw [mono_body, canon_eqD] at h
  obtain ⟨h1, h2, -⟩ := mem_scheme_tyvars.mp h
  obtain ⟨c, hc, hvc⟩ := (mem_vars_rsb _ _ v).mp h1
  rw [renumber_img] at hvc
  split at hvc
  · rw [vars_vty, List.mem_singleton] at hvc; subst hvc; rw [bndV_isBnd] at h2; cases h2
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hvc; subst hvc
    exact ⟨hc, inA_of hc h2 hm⟩

/-! ## The constraint a closure records -/

theorem PostK.addK {n0 : Nat} {C : Ctx} {st st1 : WDSt} {Chk : RSub → Prop} {K : List ConW} {k : ConW}
    (h : PostK n0 C st st1 [] Chk K) (hk : KSeg [k] st st1) :
    PostK n0 C st st1 [] (fun s => Chk s ∧ DeadC k s) (k :: K) :=
  ⟨h.seg, (fun _ h => nomatch h), (fun _ h => nomatch h),
    ⟨fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.dead k (.head _)) (h.ks.dead k'),
     fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.zone k (.head _)) (h.ks.zone k'),
     fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.old k (.head _)) (h.ks.old k')⟩,
    (fun _ h => nomatch h),
    fun s h1 h2 h3 => ⟨h.chk s h1 h2 fun k' hk' => h3 k' (.tail _ hk'), h3 k (.head _)⟩⟩

/-- The constraint recorded at a `let`: it holds now, its generalised variables are new, and the
    images of the old variables avoid them. -/
theorem kseg_closD {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st1 : WDSt} {VE0 : ValEnv}
    (hp : SPre n0 L C st) (hs : SegD n0 (Reach (th st) C st.n) st st1)
    (hok : ∀ τ ∈ veBodies VE0, OkTD st1.n τ)
    (hr : ∀ τ ∈ veBodies VE0, ∀ b ∈ (rsb (th st1) τ).vars, Reach (th st) C st.n b) :
    KSeg [((ctxRsb (th st1) C).tyvars, veBodies (rsbVE (th st1) VE0))] st st1 := by
  have hi1 := hs.inv
  have hi := hp.inv
  have hθ1 := hi1.sok
  have hsrc : ∀ b, InG ((ctxRsb (th st1) C).tyvars, veBodies (rsbVE (th st1) VE0)) b →
      ∃ τ ∈ veBodies VE0, b ∈ (rsb (th st1) τ).vars := by
    rintro b ⟨⟨τ1, hτ1, hb⟩, -⟩
    simp only [veBodies, rsbVE, List.map_map, List.mem_map, Function.comp] at hτ1
    obtain ⟨q, hq, rfl⟩ := hτ1
    exact ⟨q.2.1.body, List.mem_map.mpr ⟨q, hq, rfl⟩, hb⟩
  have hfix : ∀ b, InG ((ctxRsb (th st1) C).tyvars, veBodies (rsbVE (th st1) VE0)) b → (th st1).img b = vty b := by
    intro b hg
    obtain ⟨τ, -, hb⟩ := hsrc b hg
    obtain ⟨a, -, hba⟩ := (mem_vars_rsb _ _ b).mp hb
    exact hi1.idem a b hba
  have hA : ∀ c b, c ∈ C.tyvars → b ∈ ((th st).img c).vars → (th st1).img b = vty b →
      b ∈ (ctxRsb (th st1) C).tyvars := by
    intro c b hc hb hfb
    refine hp.inA hθ1 hc ?_
    rw [← hs.abs c]
    exact vars_rsb_of hb (by rw [hfb, vars_vty]; exact List.mem_singleton_self _)
  have hnew : ∀ b, InG ((ctxRsb (th st1) C).tyvars, veBodies (rsbVE (th st1) VE0)) b → newB st.n b = true := by
    intro b hg
    obtain ⟨τ, hτ, hb⟩ := hsrc b hg
    rcases hr τ hτ b hb with h | ⟨c, hc, hcb⟩
    · exact h
    · exact absurd (hA c b hc hcb (hfix b hg)) hg.2
  refine ⟨fun k hk b hg => ?_, fun k hk b hg => ?_, fun k hk b hg a ha hba => ?_⟩
  · simp only [List.mem_singleton] at hk; subst hk
    refine ⟨hfix b hg, fun a ha hba => ?_⟩
    rw [hp.A_fixed hθ1 hi1.idem ha, vars_vty, List.mem_singleton] at hba; subst hba
    exact hg.2 ha
  · simp only [List.mem_singleton] at hk; subst hk
    refine ⟨hnew b hg, ?_⟩
    obtain ⟨τ, hτ, hb⟩ := hsrc b hg
    exact (img_vars hi1.inv.good (hok τ hτ).old b hb).2
  · simp only [List.mem_singleton] at hk; subst hk
    have hba' : b ∈ (rsb (th st1) (vty a)).vars := by rw [rsb_vty]; exact hba
    rcases moves_ty hs.mv hs.abs hi.idem (vty a) b hba' with ⟨h1, -⟩ | ⟨e, he, -, -, hre, -, hbe⟩
    · rw [rsb_vty] at h1
      have : newB st.n b = false := by
        rcases img_old hi.inv.good a with e | ⟨-, hok'⟩
        · rw [e, vars_vty, List.mem_singleton] at h1; subst h1; exact ha
        · exact hok' b h1
      rw [hnew b hg] at this; cases this
    · rw [rsb_vty] at he
      have heo : newB st.n e = false := by
        rcases img_old hi.inv.good a with e' | ⟨-, hok'⟩
        · rw [e', vars_vty, List.mem_singleton] at he; subst he; exact ha
        · exact hok' e he
      rcases hre with h | ⟨c, hc, hce⟩
      · rw [heo] at h; cases h
      · apply hg.2
        refine hp.inA hθ1 hc ?_
        rw [← hs.abs c]
        exact vars_rsb_of hce hbe

/-! ## Group entries -/

/-- A group entry (`groupEntriesD`' first step). -/
def entryWD (C : Ctx) : Option BTy → WDM (Option (BTy × List BVar) × Ty)
  | none => do let α ← freshVD; pure ((none : Option (BTy × List BVar)), α)
  | some ty =>
    if (Stat.bTyNames ty).isEmpty && decide (Unambiguous C.U) then
      match elabTy (C.plusU []) ty with
      | some τ => if τ.vars.isEmpty then pure (some (ty, []), τ) else wdUnsupported
      | none => wdFail
    else wdUnsupported

theorem groupEntriesD_var (C : Ctx) (x : String) (ann : Option BTy) (e : BExp) (rest : Option BValBind) (st : WDSt) :
    groupEntriesD C (.var x ann e rest) st = (do
      let en ← entryWD C ann
      let es ← (match rest with | none => pure [] | some vb => groupEntriesD C vb)
      pure (en :: es)) st := by
  cases ann with
  | none => cases rest <;> rfl
  | some ty =>
    cases rest <;>
    · simp only [groupEntriesD, entryWD]
      by_cases hc : ((bTyNames ty).isEmpty && decide (Unambiguous C.U)) = true
      · rw [if_pos hc, if_pos hc]
        cases hel : elabTy (C.plusU []) ty with
        | none => rfl
        | some τ =>
          by_cases hv : τ.vars.isEmpty = true
          · simp only [hv, ↓reduceIte]
          · simp only [hv, ↓reduceIte, Bool.false_eq_true]
      · rw [if_neg hc, if_neg hc]

theorem groupEntriesD_sound {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} :
    ∀ (vb : BValBind) (st : WDSt) (es : List (Option (BTy × List BVar) × Ty)) (st' : WDSt), SPre n0 L C st →
      groupEntriesD C vb st = .ok es st' →
      (∀ e ∈ es, annU e.1 = [] ∧ ∀ (C' : Ctx) (s : RSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' e.1 (rsb s e.2) = true) ∧
      PostK n0 C st st' (es.map (·.2)) (fun _ => True) []
  | .pat _ _, st, es, st', hp, h => by unfold groupEntriesD at h; cases h
  | .var x ann e rest, st, es, st', hp, h => by
    rw [groupEntriesD_var] at h
    obtain ⟨en, st1, h1, h⟩ := wdbind_ok h
    obtain ⟨es', st2, h2, h⟩ := wdbind_ok h
    have P1 : (annU en.1 = [] ∧ ∀ (C' : Ctx) (s : RSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' en.1 (rsb s en.2) = true) ∧ PostK n0 C st st1 [en.2] (fun _ => True) [] := by
      cases ann with
      | none =>
        simp only [entryWD] at h1
        obtain ⟨α, st0, h0, h1'⟩ := wdbind_ok h1
        obtain ⟨rfl, rfl⟩ := freshVD_ok h0
        obtain ⟨rfl, rfl⟩ := pure_okD h1'
        exact ⟨⟨rfl, fun _ _ _ _ => rfl⟩, (PostK.start hp).fresh⟩
      | some ty =>
        simp only [entryWD] at h1
        by_cases hc : ((bTyNames ty).isEmpty && decide (Unambiguous C.U)) = true
        · rw [if_pos hc] at h1
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          cases hel : elabTy (C.plusU []) ty with
          | none => rw [hel] at h1; cases h1
          | some τ =>
            rw [hel] at h1
            by_cases hv : τ.vars.isEmpty = true
            · simp only [hv, ↓reduceIte] at h1
              have hv' : τ.vars = [] := by simpa using hv
              obtain ⟨rfl, rfl⟩ := pure_okD h1
              refine ⟨⟨rfl, fun C' s hU hT => ?_⟩, PostK.closed hp hv' fun _ _ => trivial⟩
              have hb : bTyNames ty = [] := by simpa using hc.1
              rw [rsb_closedD hv']
              refine checkAnn_closed hb (by rw [hU]; exact hc.2) ?_
              rw [elabTy_congrW (C1 := C'.plusU []) (C2 := C.plusU []) (by simp [Ctx.plusU, hU])
                (fun lc => by simp only [plusU_nil]; exact hT lc)]
              exact hel
            · simp only [hv, ↓reduceIte, Bool.false_eq_true] at h1; cases h1
        · rw [if_neg hc] at h1; cases h1
    have hp1 := hp.later P1.2.seg
    have P2 : (∀ e ∈ es', annU e.1 = [] ∧ ∀ (C' : Ctx) (s : RSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' e.1 (rsb s e.2) = true) ∧ PostK n0 C st1 st2 (es'.map (·.2)) (fun _ => True) [] := by
      cases rest with
      | none =>
        simp only at h2
        obtain ⟨rfl, rfl⟩ := pure_okD h2
        exact ⟨(fun _ h => nomatch h), PostK.start hp1⟩
      | some vb => exact groupEntriesD_sound vb st1 es' st2 hp1 h2
    obtain ⟨rfl, rfl⟩ := pure_okD h
    refine ⟨fun e' he' => (List.mem_cons.mp he').elim (fun e => e ▸ P1.1) (P2.1 e'), ?_⟩
    exact (PostK.seqSame hp P1.2 P2.2).weaken (covSub fun τ hτ => by simpa using hτ) fun _ _ _ => trivial

/-- A context extended by entries whose types are covered by the types a call returned. -/
theorem PostK.plusVE_pre {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st1 : WDSt} {tys : List Ty}
    {Chk : RSub → Prop} {K : List ConW} {VE : ValEnv} (hp : SPre n0 L C st) (h : PostK n0 C st st1 tys Chk K)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ q.2.2 = .v ∧ ∀ v ∈ q.2.1.body.vars, ∃ τ ∈ tys, v ∈ τ.vars) :
    SPre n0 L (C.plusVE VE) st1 ∧ (∀ b, Reach (th st1) (C.plusVE VE) st1.n b → Reach (th st) C st.n b) ∧
      AvoidK K (Reach (th st1) (C.plusVE VE) st1.n) := by
  have hq : ∀ q ∈ VE, PostK n0 C st st1 [q.2.1.body] Chk K := fun q hq =>
    h.weaken (fun τ hτ v hv => by simp only [List.mem_singleton] at hτ; subst hτ; exact (hVE q hq).2.2 v hv)
      fun _ _ c => c
  refine ⟨hp.plusVE h.seg.le h.seg.inv (fun q hq' => ?_) (fun q hq' => (hVE q hq').2.1),
    reach_plusVE h.seg hp.inv fun q hq' => (hq q hq').reach _ (.head _),
    avoid_plusVE hp h.ks fun q hq' => (hq q hq').tyav _ (.head _)⟩
  have hok := (hq q hq').okT _ (.head _)
  refine ⟨fun v hv => ?_, fun v hv _ => hok v hv⟩
  rw [(hVE q hq').1] at hv; cases hv

end WDS

end StandardElm.Stat.Complete
