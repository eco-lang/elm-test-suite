/-
  A Standard Definition of Elm? Mechanisation: L10 for W with rows (plan step 11, milestone (d)):
  the monad, instances of schemes under a later substitution (`post_instD`), lookups in the
  checker's context, and the unification of a constructor's arguments (`PostK.uargsD`).

  The canonicity that unification needs (A23) is not an invariant of W: it is supplied, when the
  checker is to accept a result, by a canonical substitution `U` absorbing the final one (in the
  root theorem, the substitution relating W's result to a canonical derivation, L11). The
  conclusions of the induction are therefore of the form "for every such `U`, canonical on the
  types recorded, the checker accepts".
-/
import StandardElmMech.Stat.Complete.WDSoundClos

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

namespace WDS

/-! ## The monad -/

theorem wdbind_ok {α β : Type} {M : WDM α} {f : α → WDM β} {st st'' : WDSt} {b : β}
    (h : (M >>= f) st = .ok b st'') : ∃ a st', M st = .ok a st' ∧ f a st' = .ok b st'' := by
  change WDM.bind M f st = _ at h
  unfold WDM.bind at h
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · cases h
  · cases h
  · cases h

theorem pure_okD {α : Type} {a b : α} {st st' : WDSt} (h : (pure a : WDM α) st = .ok b st') : b = a ∧ st' = st := by
  change WDOut.ok a st = WDOut.ok b st' at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem freshCD_ok {st st' : WDSt} {c : Cls} {t : Ty} (h : freshCD c st = .ok t st') :
    t = .var (.fresh st.n c) ∧ st' = { st with n := st.n + 1 } := by
  change WDOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem freshVD_ok {st st' : WDSt} {t : Ty} (h : freshVD st = .ok t st') :
    t = .var (.fresh st.n .any) ∧ st' = { st with n := st.n + 1 } := by
  change WDOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem freshRowD_ok {st st' : WDSt} {e : RowVar} (h : freshRowD st = .ok e st') :
    e = .fresh st.n ∧ st' = { st with n := st.n + 1 } := by
  change WDOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem getθD_ok {st st' : WDSt} {θ : RBnd} (h : getθD st = .ok θ st') : θ = st.θ ∧ st' = st := by
  change WDOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

/-! ## Canonicity supplied by a substitution absorbing the final one -/

def CnL (U : RSub) (l : List Ty) : Prop := ∀ τ ∈ l, cnB (rsb U τ) = true

/-- `U` fixes the rigid variables, respects classes and absorbs `s`. -/
def GoodU (n0 : Nat) (U s : RSub) : Prop := FixR (rigidFromD n0) U ∧ RespR U ∧ AbsS U s

theorem GoodU.cn {n0 : Nat} {U s : RSub} (h : GoodU n0 U s) {τ : Ty} (hc : cnB (rsb U τ) = true) : cnB (rsb s τ) = true :=
  cnB_of_rsb (s := U) (by rw [absS_rsb h.2.2]; exact hc)

theorem CnL.sub {U : RSub} {l l' : List Ty} (h : CnL U l) (hs : ∀ τ ∈ l', τ ∈ l) : CnL U l' := fun τ hτ => h τ (hs τ hτ)

theorem fix_bnd0D {n0 : Nat} {s : RSub} (h : FixR (rigidFromD n0) s) : s.r (.bnd 0) = ([], some (.bnd 0)) :=
  fix_row (h _ (rigidFromD_bnd n0 rfl))

theorem cnU_atpat {U : RSub} (hU : U.r (.bnd 0) = ([], some (.bnd 0))) {p : AAtPat} (h : CnL U (tysAtPat p)) :
    cnB (rsb U p.ty) = true := by
  rw [← rsbAtPat_tyD]
  refine cn_atpat_ty _ fun τ hτ => ?_
  rw [tysAtPat_sbD] at hτ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact h σ hσ

theorem cnU_pat {U : RSub} {p : APat} (h : CnL U (tysPat p)) : cnB (rsb U p.ty) = true := by
  rw [← rsbPat_tyD]
  refine cn_pat_ty _ fun τ hτ => ?_
  rw [tysPat_sbD] at hτ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ; exact h σ hσ

/-! ## Instances under a later substitution -/

theorem bindSubst_inst (s : RSub) (hs : RespR s) : ∀ (vs : List BVar) (n : Nat), ∃ S,
    bindSubst vs (rsbList s (freshFromD n vs)) = some S ∧ S.Respects ∧
      ∀ v, S.toR.img v = if v ∈ vs then s.img (instVD (n + vs.idxOf v) v) else vty v
  | [], n => ⟨Subst.id, rfl, fun _ h => by simp [Subst.id] at h, fun v => by
    cases v <;> simp [Subst.toR, Subst.id, RSub.img, FMap.find?, vty]⟩
  | .ty a :: vs, n => by
    obtain ⟨S, h1, h2, h3⟩ := bindSubst_inst s hs vs (n + 1)
    refine ⟨{ S with ty := (a, s.t (.fresh n a.cls)) :: S.ty }, ?_, fun p hp => ?_, fun v => ?_⟩
    · simp only [freshFromD, instVD, vty, rsbList, rsb, bindSubst, h1]
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hs (.fresh n a.cls)
      · exact h2 p hp
    · by_cases e : v = .ty a
      · subst e; simp [RSub.img, Subst.toR, FMap.find?, instVD]
      · have hS : (Subst.toR { S with ty := (a, s.t (.fresh n a.cls)) :: S.ty }).img v = S.toR.img v := by
          cases v with
          | ty b =>
            have : b ≠ a := fun h => e (by rw [h])
            simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
          | row _ => rfl
        rw [hS, h3]
        by_cases hm : v ∈ vs
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm), List.idxOf_cons, if_neg (by simpa using Ne.symm e)]
          congr 2; omega
        · rw [if_neg hm, if_neg (by simp [e, hm])]
  | .row e0 :: vs, n => by
    obtain ⟨S, h1, h2, h3⟩ := bindSubst_inst s hs vs (n + 1)
    refine ⟨{ S with row := (e0, s.r (.fresh n)) :: S.row }, ?_, h2, fun v => ?_⟩
    · simp only [freshFromD, instVD, vty, rsbList, rsb, RSub.tl, rsbRow, mrg_nil_left, bindSubst, h1]
    · by_cases e : v = .row e0
      · subst e; simp [RSub.img, Subst.toR, FMap.find?, instVD]
      · have hS : (Subst.toR { S with row := (e0, s.r (.fresh n)) :: S.row }).img v = S.toR.img v := by
          cases v with
          | row b =>
            have : b ≠ e0 := fun h => e (by rw [h])
            simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
          | ty _ => rfl
        rw [hS, h3]
        by_cases hm : v ∈ vs
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm), List.idxOf_cons, if_neg (by simpa using Ne.symm e)]
          congr 2; omega
        · rw [if_neg hm, if_neg (by simp [e, hm])]

/-- W's instance, with its instance list, stays an instance under a later substitution whose
    image of it is canonical. -/
theorem genAt_instD {n0 n : Nat} {σ : Scheme} {s : RSub} (hs : SOk n0 s) (hσ : SchWD n σ)
    (hc : cnB (rsb s (rsb (instS n σ.bound) σ.body)) = true) :
    genAt (rsbScheme s σ) (rsbList s (freshFromD n σ.bound)) (rsb s (rsb (instS n σ.bound) σ.body)) = true := by
  obtain ⟨S, h1, h2, h3⟩ := bindSubst_inst s hs.resp σ.bound n
  have heq : rsb S.toR (rsb s σ.body) = rsb s (rsb (instS n σ.bound) σ.body) := by
    rw [rsb_rsb, rsb_rsb]
    apply rsb_congr
    intro w hw
    rw [img_rcomp, img_rcomp, instS_img]
    by_cases hm : w ∈ σ.bound
    · rw [if_pos hm, hs.fix w (rigidFromD_bnd n0 (hσ.1 w hm)), rsb_vty, h3, if_pos hm, rsb_vty]
    · rw [if_neg hm, rsb_vty]
      refine rsb_eq_self fun u hu => ?_
      rw [h3, if_neg]
      intro hu'
      have := hs.img w (hσ.2 w hw hm).1 u hu
      rw [hσ.1 u hu'] at this; cases this
  simp only [genAt, rsbScheme, h1, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨(Subst.respectsB_iff S).mpr h2, decide_eq_true (by rw [apply_of_cn S _ (by rw [heq]; exact hc), heq])⟩

theorem SPre.ctxB {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (hp : SPre n0 L C st) :
    ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true :=
  fun x p hf => (hp.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])).1

theorem SPre.ctxF {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (hp : SPre n0 L C st) :
    ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.body.vars, v ∉ p.1.bound → v.isBnd = false :=
  fun x p hf v hv hb => ((hp.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])).2 v hv hb).1

/-- A lookup in W's context: its free variables are the context's, and the checker's context finds
    the substituted scheme. -/
theorem lookup_factsD {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (hp : SPre n0 L C st)
    {lv : LongId} {σ : Scheme} {x : IdStatus} (h : C.lookupVal lv = some (σ, x)) :
    (∀ c ∈ σ.tyvars, c ∈ C.tyvars) ∧ ∀ s, SOk n0 s → (ctxRsb s C).lookupVal lv = some (rsbScheme s σ, x) := by
  have hσ := hp.ctxW lv σ x h
  cases hq : lv.qual with
  | none =>
    have hf : FMap.find? C.E.VE lv.id = some (σ, x) := by simpa [Ctx.lookupVal, Env.lookupVal, hq] using h
    refine ⟨fun c hc => mem_ctx_tyvars.mpr (.inr ⟨lv.id, (σ, x), hf, hc⟩), fun s hs => ?_⟩
    simp only [Ctx.lookupVal, Env.lookupVal, hq]
    change FMap.find? (rsbVE s C.E.VE) lv.id = _
    rw [find?_rsbVE, hf]; rfl
  | some m =>
    have hl : (FMap.find? C.E.QE m).bind (fun I => FMap.find? I.VE lv.id) = some (σ, x) := by
      simpa [Ctx.lookupVal, Env.lookupVal, hq] using h
    have qe : ∀ c ∈ σ.tyvars, c ∈ restTv C := by
      intro c hc
      cases hI : FMap.find? C.E.QE m with
      | none => rw [hI] at hl; cases hl
      | some I =>
        rw [hI] at hl; simp only [Option.bind_some] at hl
        simp only [restTv, List.mem_append]
        left; left
        rw [mem_tyvarsBy]
        refine ⟨m, I, by simp, hI, ?_⟩
        simp only [IEnv.tyvars, List.mem_append]
        right
        exact mem_VE_tyvars.mpr ⟨lv.id, (σ, x), hl, hc⟩
    refine ⟨fun c hc => mem_ctx_tyvars.mpr (.inl (qe c hc)), fun s hs => ?_⟩
    have e1 : (ctxRsb s C).lookupVal lv = C.lookupVal lv := by
      simp [Ctx.lookupVal, Env.lookupVal, hq, ctxRsb]
    rw [e1, h]
    obtain ⟨bd, body⟩ := σ
    simp only [rsbScheme, Option.some.injEq, Prod.mk.injEq, Scheme.mk.injEq, true_and, and_true]
    symm
    refine rsb_eq_self fun w hw => ?_
    by_cases hb : w ∈ bd
    · exact hs.fix w (rigidFromD_bnd n0 (hσ.1 w hb))
    · exact hs.fix w (hp.rest w (qe w (mem_scheme_tyvars.mpr ⟨hw, (hσ.2 w hw hb).1, hb⟩)))

/-- W's instance of a scheme of its context. -/
theorem post_instD {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st' : WDSt} {σ : Scheme} {ts : List Ty}
    {τ : Ty} (hp : SPre n0 L C st) (hσ : SchWD st.n σ) (hfv : ∀ c ∈ σ.tyvars, c ∈ C.tyvars)
    (h : instantiateD σ st = .ok (ts, τ) st') :
    PostK n0 C st st' [τ] (fun s => cnB (rsb s τ) = true → genAt (rsbScheme s σ) (rsbList s ts) (rsb s τ) = true) [] := by
  obtain ⟨hts, hτ, hθ, hn⟩ := instantiateD_ok h
  have hi := hp.inv
  have hle : st.n ≤ st'.n := by omega
  have hth : th st' = th st := by simp only [th, hθ]
  have hok : OkTD st'.n τ := by rw [hτ, hn]; exact inst_okTD hσ
  -- a variable of the instance: new, or free in the scheme
  have hv : ∀ b ∈ τ.vars, newB st.n b = true ∨ b ∈ C.tyvars := by
    intro b hb
    rw [hτ] at hb
    obtain ⟨c, hc, hbc⟩ := (mem_vars_rsb _ _ b).mp hb
    rw [instS_img] at hbc
    split at hbc
    · rw [vars_vty, List.mem_singleton] at hbc; subst hbc
      left; cases c <;> simp [newB, instVD, TyVar.isNew]
    · rename_i hm
      rw [vars_vty, List.mem_singleton] at hbc; subst hbc
      exact .inr (hfv _ (mem_scheme_tyvars.mpr ⟨hc, (hσ.2 _ hc hm).1, hm⟩))
  have hinv' : SInvW n0 st' := ⟨⟨Nat.le_trans hi.inv.le hle, by rw [hθ]; exact goodR_mono hi.inv.good hle⟩,
    by rw [hθ]; exact hi.nb⟩
  refine ⟨⟨hle, hinv', by rw [hth]; exact absS_self hi.idem, by rw [hth]; exact moves_refl _ _⟩,
    fun τ' hτ' => ?_, fun τ' hτ' b hb' => ?_, KSeg.nil _ _, (fun _ _ _ h => nomatch h), fun s hs _ _ hc => ?_⟩
  · simp only [List.mem_singleton] at hτ'; subst hτ'; exact hok
  · simp only [List.mem_singleton] at hτ'; subst hτ'
    rw [hth] at hb'
    obtain ⟨a, ha, hba⟩ := (mem_vars_rsb _ _ b).mp hb'
    rcases hv a ha with h1 | h1
    · rw [hi.unbound_new h1, vars_vty, List.mem_singleton] at hba; subst hba
      exact .inl h1
    · exact .inr ⟨a, h1, hba⟩
  · subst hτ; subst hts
    exact genAt_instD hs hσ hc

/-! ## Unifying lists -/

theorem unifyArgsD_length {fuel : Nat} {R : RRigid} : ∀ {l1 l2 : List Ty} {st st' : WDSt} {u : Unit},
    unifyArgsD fuel R l1 l2 st = .ok u st' → l1.length = l2.length
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, _, h => by
    unfold Complete.unifyArgsD at h
    obtain ⟨_, _, _, h2⟩ := wdbind_ok h
    simp only [List.length_cons, unifyArgsD_length h2]
  | [], _ :: _, _, _, _, h => by unfold Complete.unifyArgsD at h; cases h
  | _ :: _, [], _, _, _, h => by unfold Complete.unifyArgsD at h; cases h

theorem cnB_arrows {r : Ty} (hr : cnB r = true) : ∀ {l : List Ty}, (∀ x ∈ l, cnB x = true) → cnB (arrows l r) = true
  | [], _ => hr
  | x :: l, h => by
    simp only [arrows, cnB, Bool.and_eq_true]
    exact ⟨h x (.head _), cnB_arrows hr fun y hy => h y (.tail _ hy)⟩

/-- Canonicity down an absorption chain. -/
theorem cn_down {U s θ : RSub} (h1 : AbsS U s) (h2 : AbsS s θ) {τ : Ty} (hc : cnB (rsb U τ) = true) :
    cnB (rsb θ τ) = true :=
  cnB_of_rsb (s := U) (by rw [absS_rsb (absS_trans h1 h2)]; exact hc)

/-- A canonical unifier of the pairs absorbing the substitution of the state. -/
def UPrem (n0 : Nat) (st : WDSt) (l1 l2 : List Ty) : Prop :=
  l1.length = l2.length ∧ ∃ U, FixR (rigidFromD n0) U ∧ RespR U ∧ AbsR U st.θ ∧
    ∀ p ∈ l1.zip l2, rsb U p.1 = rsb U p.2 ∧ cnB (rsb U p.1) = true

theorem rsbList_cons (s : RSub) (x : Ty) (l : List Ty) : rsbList s (x :: l) = rsb s x :: rsbList s l := rfl

theorem PostK.uargsD {fuel n0 : Nat} {C : Ctx} {st : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW} :
    ∀ (l1 l2 : List Ty) (st2 st3 : WDSt) (u : Unit), PostK n0 C st st2 tys Chk K → Cov (l1 ++ l2) tys →
      unifyArgsD fuel (rigidFromD n0) l1 l2 st2 = .ok u st3 →
      PostK n0 C st st3 tys (fun s => Chk s ∧ AbsS s (th st2) ∧ (UPrem n0 st2 l1 l2 → rsbList s l1 = rsbList s l2)) K
  | [], [], st2, st3, u, h, _, hu => by
    unfold Complete.unifyArgsD at hu
    obtain ⟨-, rfl⟩ := pure_okD hu
    exact h.withAbs.weaken (cov_refl _) fun s _ hs => ⟨hs.1, hs.2, fun _ => rfl⟩
  | t :: l1, u' :: l2, st2, st3, u, h, hc, hu => by
    unfold Complete.unifyArgsD at hu
    obtain ⟨_, st4, h1, h2⟩ := wdbind_ok hu
    have hc1 : Cov [t, u'] tys := fun τ hτ v hv => hc τ (by simp at hτ; rcases hτ with rfl | rfl <;> simp) v hv
    have hc2 : Cov (l1 ++ l2) tys := fun τ hτ v hv => hc τ (by
      rcases List.mem_append.mp hτ with h | h <;> simp [h]) v hv
    have P1 := h.unify hc1 h1
    have P2 := PostK.uargsD l1 l2 st4 st3 u P1 hc2 h2
    have hi2 := h.seg.inv
    have ok1 : OkTD st2.n t := fun v hv => by
      obtain ⟨τ', h1', h2'⟩ := hc t (by simp) v hv; exact h.okT τ' h1' v h2'
    have ok2 : OkTD st2.n u' := fun v hv => by
      obtain ⟨τ', h1', h2'⟩ := hc u' (by simp) v hv; exact h.okT τ' h1' v h2'
    have okL : ∀ x ∈ l1 ++ l2, OkTD st2.n x := fun x hx v hv => by
      obtain ⟨τ', h1', h2'⟩ := hc x (by simp at hx ⊢; rcases hx with hx | hx <;> simp [hx]) v hv
      exact h.okT τ' h1' v h2'
    refine P2.weaken (cov_refl _) fun s _ ⟨⟨c0, hab2, he⟩, _, hr⟩ => ⟨c0, hab2, fun ⟨hlen, U, hfx, hre, hab, hU⟩ => ?_⟩
    have hU1 := hU (t, u') (by simp)
    have c1 : cnB (rsb (th st2) t) = true := cnB_of_rsb (s := U) (by rw [absR_rsb hab]; exact hU1.2)
    have c2 : cnB (rsb (th st2) u') = true := cnB_of_rsb (s := U) (by rw [absR_rsb hab, ← hU1.1]; exact hU1.2)
    obtain ⟨-, -, -, hcomp⟩ := unifyWD_ok (newFlexR_rigidFromD hi2.inv.le) hi2.inv.good ok1.old ok2.old c1 c2 h1
    obtain ⟨U', hag, hre', hab'⟩ := hcomp U hfx hre hU1.1 hU1.2 hab
    have hfx' : FixR (rigidFromD n0) U' := fixR_of_agree (newFlexR_rigidFromD hi2.inv.le) hfx hag
    have hrest : UPrem n0 st4 l1 l2 := ⟨by simpa using hlen, U', hfx', hre', hab', fun p hp => by
      have hm := List.of_mem_zip hp
      have hp' := hU p (List.mem_cons_of_mem _ hp)
      have e1 : rsb U' p.1 = rsb U p.1 := rsb_agreeD (okL p.1 (List.mem_append_left _ hm.1)).old hag
      have e2 : rsb U' p.2 = rsb U p.2 := rsb_agreeD (okL p.2 (List.mem_append_right _ hm.2)).old hag
      rw [e1, e2]; exact hp'⟩
    rw [rsbList_cons, rsbList_cons, he c1 c2, hr hrest]
  | [], _ :: _, _, _, _, _, _, hu => by unfold Complete.unifyArgsD at hu; cases hu
  | _ :: _, [], _, _, _, _, _, hu => by unfold Complete.unifyArgsD at hu; cases hu

end WDS

end StandardElm.Stat.Complete
