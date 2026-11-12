/-
  A Standard Definition of Elm? Mechanisation: L10 for patterns and occurrences (plan step 11,
  milestone (b), section 8): what W builds for a pattern is accepted by the checker under every
  later substitution (`wAtPat_sound` and the others), and so is an occurrence's instance
  (`post_inst`, `genAt_inst`).
-/
import StandardElmMech.Stat.Complete.WSoundClos

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## The monad -/

theorem wbind_ok {α β : Type} {M : WM α} {f : α → WM β} {st st'' : WSt} {b : β}
    (h : (M >>= f) st = .ok b st'') : ∃ a st', M st = .ok a st' ∧ f a st' = .ok b st'' := by
  change WM.bind M f st = _ at h
  unfold WM.bind at h
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · cases h
  · cases h
  · cases h

theorem freshC_ok {st st' : WSt} {c : Cls} {t : Ty} (h : freshC c st = .ok t st') :
    t = .var (.fresh st.n c) ∧ st' = { st with n := st.n + 1 } := by
  change WOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem pure_ok' {α : Type} {a b : α} {st st' : WSt} (h : (pure a : WM α) st = .ok b st') : b = a ∧ st' = st := by
  change WOut.ok a st = WOut.ok b st' at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem freshV_ok {st st' : WSt} {t : Ty} (h : freshV st = .ok t st') :
    t = .var (.fresh st.n .any) ∧ st' = { st with n := st.n + 1 } := by
  change WOut.ok _ _ = _ at h
  injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

/-! ## Instances under a later substitution -/

theorem lk_zip_sb {s : FSub} : ∀ (as : List TyVar) (ts : List Ty) (a : TyVar), as.length = ts.length →
    (a ∉ as → s a = .var a) → lk (as.zip (sbList s ts)) a = sb s (lk (as.zip ts) a)
  | [], [], a, _, h => by simp only [List.zip_nil_left, lk_nil, sb]; exact (h List.not_mem_nil).symm
  | b :: bs, t :: ts, a, hl, h => by
    simp only [sbList, List.zip_cons_cons, lk_cons]
    by_cases e : b = a
    · simp [e]
    · simp only [e, ↓reduceIte]
      exact lk_zip_sb bs ts a (by simpa using hl) fun hm => h fun hm' =>
        (List.mem_cons.mp hm').elim (fun e' => e e'.symm) hm
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

theorem zip_freshFrom : ∀ (n : Nat) (as : List TyVar), ∀ p ∈ as.zip (freshFrom n as),
    ∃ k, p.2 = .var (.fresh k p.1.cls)
  | _, [], _, h => by cases h
  | n, a :: as, p, h => by
    simp only [freshFrom, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨n, rfl⟩
    · exact zip_freshFrom (n + 1) as p h

/-- An instance W records stays an instance, with its instance list, under a later substitution. -/
theorem genAt_inst {n0 n : Nat} {σ : Scheme} {as : List TyVar} {ts : List Ty} {s : FSub}
    (hb : σ.bound = as.map BVar.ty) (hσ : SchW n σ) (hl : as.length = ts.length)
    (hts : ∀ p ∈ as.zip ts, Adm p.1.cls (sb s p.2))
    (hs : SOk n0 s) : genAt (sbScheme s σ) (sbList s ts) (sb s (sb (lk (as.zip ts)) σ.body)) = true := by
  have hl' : as.length = (sbList s ts).length := by rw [sbList_length]; exact hl
  simp only [genAt, sbScheme, hb, bindSubst_of_length hl', apply_ofBnd, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [Subst.respectsB_iff]
    intro p hp
    simp only [ofBnd, sbList_eq, List.zip_map_right, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hts q hq
  · congr 1
    rw [sb_sb, sb_sb]
    apply sb_congr
    intro a ha
    simp only [comp]
    by_cases hm : a ∈ as
    · have hab : (BVar.ty a).isBnd = true := hσ.1 (.ty a) (by rw [hb]; exact List.mem_map_of_mem hm)
      have hsa : s a = .var a := by
        cases a with
        | bnd i c => exact hs.bnd i c
        | _ => simp [BVar.isBnd] at hab
      rw [hsa]; simp only [sb]
      exact lk_zip_sb as ts a hl (fun h => absurd hm h)
    · rw [instance_of_fresh.lk_zip_not_mem hm]; simp only [sb]
      obtain ⟨a', e, hab, -⟩ := hσ.2 _ ha (by rw [hb]; simpa using hm)
      cases e
      refine sb_eq_self_iff.mpr fun c hc => ?_
      apply instance_of_fresh.lk_zip_not_mem
      intro hcm
      have := hσ.1 (.ty c) (by rw [hb]; exact List.mem_map_of_mem hcm)
      obtain ⟨c', e', hc'⟩ := hs.2 _ hab _ hc
      cases e'
      cases c <;> simp_all [BVar.isBnd, TyVar.isBndT]

/-- A lookup in W's context: its free variables are the context's, and the checker's context
    (the later substitution applied) finds the substituted scheme. -/
theorem lookup_facts {n0 : Nat} {C : Ctx} {st : WSt} (hp : SPre n0 C st) {lv : LongId} {σ : Scheme}
    {x : IdStatus} (h : C.lookupVal lv = some (σ, x)) :
    (∀ c, BVar.ty c ∈ σ.tyvars → BVar.ty c ∈ C.tyvars) ∧
      ∀ s, SOk n0 s → (ctxSb s C).lookupVal lv = some (sbScheme s σ, x) := by
  have hσ := hp.ctxW lv σ x h
  cases hq : lv.qual with
  | none =>
    have hf : FMap.find? C.E.VE lv.id = some (σ, x) := by simpa [Ctx.lookupVal, Env.lookupVal, hq] using h
    refine ⟨fun c hc => mem_ctx_tyvars.mpr (.inr ⟨lv.id, (σ, x), hf, hc⟩), fun s hs => ?_⟩
    simp only [Ctx.lookupVal, Env.lookupVal, hq]
    change FMap.find? (sbVE s C.E.VE) lv.id = _
    rw [find?_sbVE, hf]; rfl
  | some m =>
    have hl : (FMap.find? C.E.QE m).bind (fun I => FMap.find? I.VE lv.id) = some (σ, x) := by
      simpa [Ctx.lookupVal, Env.lookupVal, hq] using h
    have qe : ∀ c, BVar.ty c ∈ σ.tyvars → BVar.ty c ∈ restTv C := by
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
    have e1 : (ctxSb s C).lookupVal lv = C.lookupVal lv := by
      simp [Ctx.lookupVal, Env.lookupVal, hq, ctxSb]
    rw [e1, h]
    obtain ⟨bd, body⟩ := σ
    simp only [sbScheme, Option.some.injEq, Prod.mk.injEq, Scheme.mk.injEq, true_and, and_true]
    symm
    refine sb_eq_self_iff.mpr fun a ha => ?_
    by_cases hb : BVar.ty a ∈ bd
    · have := hσ.1 _ hb
      cases a with
      | bnd i c => exact hs.bnd i c
      | _ => simp [BVar.isBnd] at this
    · obtain ⟨a', e, hab, -⟩ := hσ.2 _ ha hb
      cases e
      exact hs.1 _ (hp.rest _ (qe _ (mem_scheme_tyvars.mpr ⟨ha, isBnd_ty hab, hb⟩)))

/-- W's instance of a scheme of its context. -/
theorem post_inst {n0 : Nat} {C : Ctx} {st st' : WSt} {σ : Scheme} {ts : List Ty} {τ : Ty}
    (hp : SPre n0 C st) (hσ : SchW st.n σ) (hfv : ∀ c, BVar.ty c ∈ σ.tyvars → BVar.ty c ∈ C.tyvars)
    (h : instantiate σ st = .ok (ts, τ) st') :
    PostK n0 C st st' [τ] (fun s => genAt (sbScheme s σ) (sbList s ts) (sb s τ) = true) [] := by
  obtain ⟨as, hb, hts, hτ, hθ, hn⟩ := instantiate_ok h
  have hθ' : lk st'.θ = lk st.θ := by rw [hθ]
  have hi := hp.inv
  have hle : st.n ≤ st'.n := by omega
  have hok : OkT st'.n τ := by rw [hτ, hts, hn]; exact inst_okT hσ hb
  -- a variable of the instance: fresh, or free in the scheme
  have hv : ∀ a, TV a τ → a.isNew st.n = true ∨ BVar.ty a ∈ C.tyvars := by
    intro a ha
    rw [hτ, hts] at ha
    obtain ⟨c, hc, hac⟩ := tyvar_sb ha
    rw [lk_zip_fresh] at hac
    split at hac
    · simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hac; subst hac
      exact .inl (by simp [TyVar.isNew])
    · rename_i hm
      simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hac; subst hac
      obtain ⟨a', e, hab, -⟩ := hσ.2 _ hc (by rw [hb]; simpa using hm)
      cases e
      exact .inr (hfv _ (mem_scheme_tyvars.mpr ⟨hc, isBnd_ty hab, by rw [hb]; simpa using hm⟩))
  refine ⟨⟨hle, ⟨Nat.le_trans hi.le hle, (by rw [hθ]; exact hi.good.mono hle), (by rw [hθ]; exact hi.okL.mono hle)⟩,
      (by rw [hθ']; exact hp.any), (by rw [hθ']; exact absorbs_self hi.good.idem), (by rw [hθ']; exact moves_refl _ _)⟩,
    fun τ' hτ' => ?_, fun τ' hτ' b hb' => ?_, KSeg.nil _ _, (fun _ _ _ h => nomatch h), fun s hs _ _ => ?_⟩
  · simp only [List.mem_singleton] at hτ'; subst hτ'
    exact ⟨hok, fun _ _ => trivial⟩
  · simp only [List.mem_singleton] at hτ'; subst hτ'
    rw [hθ'] at hb'
    obtain ⟨a, ha, hba⟩ := tyvar_sb hb'
    rcases hv a ha with h1 | h1
    · have : lk st.θ a = .var a := by
        rcases hi.ok a with e | ⟨e, -⟩
        · exact e
        · rw [h1] at e; cases e
      rw [this] at hba; simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hba; subst hba
      exact .inl h1
    · exact .inr ⟨a, h1, hba⟩
  · rw [hτ, hts]
    exact genAt_inst hb hσ (freshFrom_length _ _).symm (fun p hp => by
      obtain ⟨k, e⟩ := zip_freshFrom _ _ p hp
      rw [e]; exact hs.resp (.fresh k p.1.cls)) hs

/-! ## Unifying lists -/

theorem PostK.uargs {fuel n0 : Nat} {C : Ctx} {st : WSt} {tys : List Ty} {Chk : FSub → Prop} {K : List ConW} :
    ∀ (l1 l2 : List Ty) (st2 st3 : WSt) (u : Unit), PostK n0 C st st2 tys Chk K → Cov (l1 ++ l2) tys →
      unifyArgs fuel (rigidFrom n0) l1 l2 st2 = .ok u st3 →
      PostK n0 C st st3 tys (fun s => Chk s ∧ sbList s l1 = sbList s l2) K
  | [], [], st2, st3, u, h, _, hu => by
    unfold Complete.unifyArgs at hu
    obtain ⟨-, rfl⟩ := pure_ok' hu
    exact h.weaken (fun τ hτ v hv => ⟨τ, hτ, hv⟩) fun s _ hs => ⟨hs, rfl⟩
  | t :: l1, u' :: l2, st2, st3, u, h, hc, hu => by
    unfold Complete.unifyArgs at hu
    obtain ⟨_, st4, h1, h2⟩ := wbind_ok hu
    have hc1 : Cov [t, u'] tys := fun τ hτ v hv => hc τ (by simp at hτ; rcases hτ with rfl | rfl <;> simp) v hv
    have hc2 : Cov (l1 ++ l2) tys := fun τ hτ v hv => hc τ (by
      rcases List.mem_append.mp hτ with h | h <;> simp [h]) v hv
    have p1 := h.unify hc1 h1
    have p2 := PostK.uargs l1 l2 st4 st3 u p1 hc2 h2
    exact p2.weaken (fun τ hτ v hv => ⟨τ, hτ, hv⟩) fun s _ ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, by simp [sbList, h2, h3]⟩
  | [], _ :: _, _, _, _, _, _, hu => by unfold Complete.unifyArgs at hu; cases hu
  | _ :: _, [], _, _, _, _, _, hu => by unfold Complete.unifyArgs at hu; cases hu

/-! ## Patterns -/

theorem tysAtPats_mem {a : AAtPat} {l : List AAtPat} {τ : Ty} (ha : a ∈ l) (hτ : τ ∈ tysAtPat a) :
    τ ∈ tysAtPats l := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [tysAtPats, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact .inl hτ
    · exact .inr (ih ha)

theorem peel_eq {k : Nat} {τ : Ty} {τs : List Ty} {r : Ty} (h : peel k τ = some (τs, r)) : τ = arrows τs r := by
  have := (peel_sb (s := idS) k τ τs r h).2
  rwa [sb_id, sb_id, sbList_id] at this

theorem cov_listTy {τ : Ty} {l : List Ty} (h : ∀ v ∈ τ.vars, ∃ τ' ∈ l, v ∈ τ'.vars) : Cov [listTy τ] l := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  simp only [listTy, Ty.vars, Ty.listVars, List.append_nil] at hv
  exact h v hv

mutual
theorem wAtPat_sound (fuel n0 : Nat) : ∀ (p : BAtPat) (C : Ctx) (st : WSt) (r : Ty × AAtPat) (st' : WSt),
    SPre n0 C st → wAtPat fuel (rigidFrom n0) C p st = .ok r st' →
    r.1 = r.2.ty ∧ PostK n0 C st st' (tysAtPat r.2) (fun s => checkAtPat (ctxSb s C) (sbAtPat s r.2) = true) []
  | .wild, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wbind_ok h
    obtain ⟨rfl, rfl⟩ := freshV_ok h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h2
    exact ⟨rfl, (PostK.start hp).fresh.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ) fun _ _ _ => rfl⟩
  | .var x, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wbind_ok h
    obtain ⟨rfl, rfl⟩ := freshV_ok h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h2
    exact ⟨rfl, (PostK.start hp).fresh.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ) fun _ _ _ => rfl⟩
  | .scon sc, C, st, r, st', hp, h => by
    cases sc with
    | int k =>
      simp only [wAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨rfl, PostK.closed hp rfl fun s _ => by
        show checkAtPat _ (.scon _ (sb s tIntTy)) = true; rw [sb_closed rfl]; rfl⟩
    | char c =>
      simp only [wAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨rfl, PostK.closed hp rfl fun s _ => by
        show checkAtPat _ (.scon _ (sb s tCharTy)) = true; rw [sb_closed rfl]; rfl⟩
    | str c =>
      simp only [wAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
      exact ⟨rfl, PostK.closed hp rfl fun s _ => by
        show checkAtPat _ (.scon _ (sb s tStringTy)) = true; rw [sb_closed rfl]; rfl⟩
    | float m e => simp only [wAtPat] at h; cases h
  | .con lc, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h
      cases x with
      | v => cases h
      | c =>
      dsimp only at h
      obtain ⟨⟨ts, τ⟩, st1, h1, h2⟩ := wbind_ok h
      have hpi := post_inst hp (hp.ctxW _ _ _ hl) (lookup_facts hp hl).1 h1
      dsimp only at h2
      split at h2
      · obtain ⟨rfl, rfl⟩ := pure_ok' h2
        refine ⟨rfl, hpi.weaken (covSub fun τ hτ => by simpa [tysAtPat] using hτ) fun s hs hg => ?_⟩
        simp only [checkAtPat, sbAtPat, (lookup_facts hp hl).2 s hs, hg, Bool.true_and]
        simp [sb, isConTy]
      · cases h2
      · cases h2
  | .unit, C, st, r, st', hp, h => by
    simp only [wAtPat] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨rfl, (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysAtPat] at hτ) fun _ _ _ => rfl⟩
  | .tuple p1 p2 p3, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨⟨τ2, a2⟩, st2, h2, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨⟨τ3, a3⟩, st3, h3, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p1 C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wPat_sound fuel n0 p2 C st1 _ st2 (hp.later P1.seg) h2
    have P12 := P1.seq P2 (reach_same P1.seg hp.inv) (avoid_same hp P1.ks)
    obtain ⟨e3, P3⟩ := wPatOpt_sound fuel n0 p3 C st2 _ st3 (hp.later P12.seg) h3
    have P123 := P12.seq P3 (reach_same P12.seg hp.inv) (avoid_same hp P12.ks)
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    refine ⟨by simp only at e1 e2 e3; simp [AAtPat.ty, e1, e2, e3], ?_⟩
    exact P123.weaken (cov_refl _) fun s _ ⟨⟨c1, c2⟩, c3⟩ => by simp [checkAtPat, sbAtPat, c1, c2, c3]
  | .nil, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    obtain ⟨α, st1, h1, h2⟩ := wbind_ok h
    obtain ⟨rfl, rfl⟩ := freshV_ok h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h2
    refine ⟨rfl, (PostK.start hp).fresh.weaken (cov_listTy fun v hv => ⟨_, by simp, hv⟩) fun s _ _ => ?_⟩
    simp [checkAtPat, sbAtPat, isListTy, listTy, sb, sbList]
  | .record _, C, st, r, st', hp, h => by simp only [wAtPat] at h; cases h
  | .paren p, C, st, r, st', hp, h => by
    simp only [wAtPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c => by simpa [checkAtPat, sbAtPat] using c⟩
theorem wPat_sound (fuel n0 : Nat) : ∀ (p : BPat) (C : Ctx) (st : WSt) (r : Ty × APat) (st' : WSt),
    SPre n0 C st → wPat fuel (rigidFrom n0) C p st = .ok r st' →
    r.1 = r.2.ty ∧ PostK n0 C st st' (tysPat r.2) (fun s => checkPat (ctxSb s C) (sbPat s r.2) = true) []
  | .atpat a, C, st, r, st', hp, h => by
    simp only [wPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wAtPat_sound fuel n0 a C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c => by simpa [checkPat, sbPat] using c⟩
  | .con lc args, C, st, r, st', hp, h => by
    simp only [wPat] at h
    cases hl : C.lookupVal lc with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨σ, x⟩ := p
      rw [hl] at h
      cases x with
      | v => cases h
      | c =>
      dsimp only at h
      obtain ⟨⟨ts, τb⟩, st1, h1, h⟩ := wbind_ok h
      dsimp only at h
      have hpi := post_inst hp (hp.ctxW _ _ _ hl) (lookup_facts hp hl).1 h1
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
        have hτb := peel_eq hpeel
        obtain ⟨ps, st2, h2, h⟩ := wbind_ok h
        obtain ⟨_, st3, h3, h⟩ := wbind_ok h
        obtain ⟨e2, P2⟩ := wAtPats_sound fuel n0 args C st1 ps st2 (hp.later hpi.seg) h2
        have P12 := hpi.seq P2 (reach_same hpi.seg hp.inv) (avoid_same hp hpi.ks)
        have hmap : ps.map (·.1) = AAtPat.tyList (ps.map (·.2)) := by
          rw [tyList_eq_map, List.map_map]
          exact List.map_congr_left fun p hp' => e2 p hp'
        have hc : Cov (ps.map (·.1) ++ τs) ([τb] ++ tysAtPats (ps.map (·.2))) := by
          intro x hx v hv
          rcases List.mem_append.mp hx with hx | hx
          · rw [hmap, tyList_eq_map] at hx
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            obtain ⟨τ', h1', h2'⟩ := atpat_ty_vars a v hv
            exact ⟨τ', List.mem_append_right _ (tysAtPats_mem ha h1'), h2'⟩
          · exact ⟨τb, by simp, by rw [hτb]; exact arrows_vars_left hx hv⟩
        have P3 := P12.uargs _ _ _ _ _ hc h3
        obtain ⟨rfl, rfl⟩ := pure_ok' h
        refine ⟨rfl, P3.weaken ?_ fun s hs ⟨⟨hg, hcs⟩, he⟩ => ?_⟩
        · intro x hx v hv
          simp only [tysPat, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨τb, by simp, by rw [hτb]; exact arrows_vars_right hv⟩
          · exact ⟨x, List.mem_append_right _ hx, hv⟩
        · simp only [checkPat, sbPat, (lookup_facts hp hl).2 s hs, Bool.and_eq_true]
          refine ⟨⟨?_, by simp [sb, isConTy]⟩, hcs⟩
          rw [sbAtPats_tyList, ← hmap, he, ← (peel_sb (s := s) _ _ _ _ hpeel).2]
          exact hg
  | .cons p1 p2, C, st, r, st', hp, h => by
    simp only [wPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, k1⟩ := wbind_ok h
    dsimp only at k1
    obtain ⟨⟨τ2, a2⟩, st2, h2, k2⟩ := wbind_ok k1
    dsimp only at k2
    obtain ⟨_, st3, h3, k3⟩ := wbind_ok k2
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p1 C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wPat_sound fuel n0 p2 C st1 _ st2 (hp.later P1.seg) h2
    simp only at e1 e2; subst e1; subst e2
    have P12 := P1.seq P2 (reach_same P1.seg hp.inv) (avoid_same hp P1.ks)
    have hc : Cov [a2.ty, listTy a1.ty] (tysPat a1 ++ tysPat a2) := by
      intro x hx v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · obtain ⟨τ', h1', h2'⟩ := pat_ty_vars a2 v hv; exact ⟨τ', List.mem_append_right _ h1', h2'⟩
      · simp only [listTy, Ty.vars, Ty.listVars, List.append_nil] at hv
        obtain ⟨τ', h1', h2'⟩ := pat_ty_vars a1 v hv; exact ⟨τ', List.mem_append_left _ h1', h2'⟩
    have P3 := P12.unify hc h3
    obtain ⟨rfl, rfl⟩ := pure_ok' k3
    refine ⟨rfl, P3.weaken (cov_refl _) fun s _ ⟨⟨c1, c2⟩, he⟩ => ?_⟩
    simp only [checkPat, sbPat, c1, c2, Bool.true_and, decide_eq_true_eq, sbPat_ty, he, listTy_sb]
  | .as p x, C, st, r, st', hp, h => by
    simp only [wPat] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨e1, P1.weaken (cov_refl _) fun s _ c => by simpa [checkPat, sbPat] using c⟩
theorem wPatOpt_sound (fuel n0 : Nat) : ∀ (p : Option BPat) (C : Ctx) (st : WSt) (r : Option Ty × Option APat)
    (st' : WSt), SPre n0 C st → wPatOpt fuel (rigidFrom n0) C p st = .ok r st' →
    r.1 = APat.tyOpt r.2 ∧ PostK n0 C st st' (tysPatOpt r.2) (fun s => checkPatOpt (ctxSb s C) (sbPatOpt s r.2) = true) []
  | none, C, st, r, st', hp, h => by
    simp only [wPatOpt] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨rfl, (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysPatOpt] at hτ) fun _ _ _ => rfl⟩
  | some p, C, st, r, st', hp, h => by
    simp only [wPatOpt] at h
    obtain ⟨⟨τ1, a1⟩, st1, h1, h⟩ := wbind_ok h
    dsimp only at h
    obtain ⟨e1, P1⟩ := wPat_sound fuel n0 p C st _ st1 hp h1
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨by simp only at e1; simp [APat.tyOpt, e1], P1.weaken (cov_refl _) fun s _ c => by simpa [checkPatOpt, sbPatOpt] using c⟩
theorem wAtPats_sound (fuel n0 : Nat) : ∀ (l : List BAtPat) (C : Ctx) (st : WSt) (r : List (Ty × AAtPat))
    (st' : WSt), SPre n0 C st → wAtPats fuel (rigidFrom n0) C l st = .ok r st' →
    (∀ p ∈ r, p.1 = p.2.ty) ∧ PostK n0 C st st' (tysAtPats (r.map (·.2)))
      (fun s => checkAtPatList (ctxSb s C) (sbAtPats s (r.map (·.2))) = true) []
  | [], C, st, r, st', hp, h => by
    simp only [wAtPats] at h; obtain ⟨rfl, rfl⟩ := pure_ok' h
    exact ⟨(fun _ h => nomatch h), (PostK.start hp).weaken (covSub fun τ hτ => by simp [tysAtPats] at hτ)
      fun _ _ _ => rfl⟩
  | a :: as, C, st, r, st', hp, h => by
    simp only [wAtPats] at h
    obtain ⟨r1, st1, h1, h⟩ := wbind_ok h
    obtain ⟨rs, st2, h2, h⟩ := wbind_ok h
    obtain ⟨e1, P1⟩ := wAtPat_sound fuel n0 a C st _ st1 hp h1
    obtain ⟨e2, P2⟩ := wAtPats_sound fuel n0 as C st1 _ st2 (hp.later P1.seg) h2
    have P12 := P1.seq P2 (reach_same P1.seg hp.inv) (avoid_same hp P1.ks)
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    refine ⟨fun p hp' => ?_, P12.weaken (cov_refl _) fun s _ ⟨c1, c2⟩ => ?_⟩
    · rcases List.mem_cons.mp hp' with rfl | hp'
      · exact e1
      · exact e2 p hp'
    · simp [checkAtPatList, sbAtPats, c1, c2]
end


end StandardElm.Stat.Complete
