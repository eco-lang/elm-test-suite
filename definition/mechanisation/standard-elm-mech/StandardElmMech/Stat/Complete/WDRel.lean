/-
  A Standard Definition of Elm? Mechanisation: the relation between W's context and the context
  of a derivation, for the main induction L11 with records and rows (plan step 11, milestone (d),
  section 8): WRel.lean for substitutions of type and row variables (`RSub`).

  * `SchRelD s σ σ'`: the free variables of `s σ` are free in `σ'` (`FtvRelD`), and every
    instance of `σ'` is an instance of `s σ` (`InstUnderD`: `σ`'s body with its bound variables,
    type or row, replaced by the images of a substitution admissible on the bound type variables,
    its free variables by their images under `s`). Every scheme is covered: W instantiates bound
    row variables (with a fresh row variable).
  * `CtxRelD P R C C'`: as `CtxRel`, with rigid variables of both sorts.

  Lemmas: lookups, the free variables of related contexts, extension, and a scheme related to
  itself (`schRel_reflD`, through the bridge `gen_rsb`).
-/
import StandardElmMech.Stat.Complete.WDBasics
import StandardElmMech.Stat.Complete.WDBridge

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Instances under a substitution -/

/-- `g` on the bound variables of `σ`, `s` on the others. -/
def extS (σ : Scheme) (g s : RSub) : RSub :=
  ⟨fun a => if BVar.ty a ∈ σ.bound then g.t a else s.t a,
   fun e => if BVar.row e ∈ σ.bound then g.r e else s.r e⟩

theorem extS_img (σ : Scheme) (g s : RSub) (v : BVar) :
    (extS σ g s).img v = if v ∈ σ.bound then g.img v else s.img v := by
  cases v with
  | ty a => by_cases h : BVar.ty a ∈ σ.bound <;> simp [RSub.img, extS, h]
  | row e => by_cases h : BVar.row e ∈ σ.bound <;> simp [RSub.img, extS, h]

/-- `τ` is an instance of `s σ`: the bound variables replaced by images admissible for their
    classes. -/
def InstUnderD (s : RSub) (σ : Scheme) (τ : Ty) : Prop :=
  ∃ g : RSub, (∀ a, BVar.ty a ∈ σ.bound → Adm a.cls (g.t a)) ∧ τ = rsb (extS σ g s) σ.body

def FtvRelD (s : RSub) (σ σ' : Scheme) : Prop :=
  ∀ w ∈ σ.tyvars, ∀ v ∈ (s.img w).tyvars, v ∈ σ'.tyvars

def SchRelD (s : RSub) (σ σ' : Scheme) : Prop :=
  FtvRelD s σ σ' ∧ ∀ τ, Gen σ' τ → InstUnderD s σ τ

def CtxRelD (P : Scheme → Scheme → Prop) (R : RRigid) (C C' : Ctx) : Prop :=
  C.T = C'.T ∧ C.U = C'.U ∧ C.E.QE = C'.E.QE ∧ C.E.TE = C'.E.TE ∧ VEMatch P C.E.VE C'.E.VE ∧
    ∀ v ∈ restTv C, R v = true

/-! ## Schemes W puts in its contexts -/

/-- Bound variables `bnd`; the free variables of the body not `bnd`, below `n`. -/
def SchWD (n : Nat) (σ : Scheme) : Prop :=
  (∀ v ∈ σ.bound, v.isBnd = true) ∧ ∀ v ∈ σ.body.vars, v ∉ σ.bound → v.isBnd = false ∧ newB n v = false

def CtxWD (n : Nat) (C : Ctx) : Prop := ∀ lv σ st, C.lookupVal lv = some (σ, st) → SchWD n σ

theorem SchWD.mono {n m : Nat} (h : n ≤ m) {σ : Scheme} (hσ : SchWD n σ) : SchWD m σ :=
  ⟨hσ.1, fun v hv hb => ⟨(hσ.2 v hv hb).1, newB_mono h (hσ.2 v hv hb).2⟩⟩

theorem CtxWD.mono {n m : Nat} (h : n ≤ m) {C : Ctx} (hC : CtxWD n C) : CtxWD m C :=
  fun lv σ st hl => (hC lv σ st hl).mono h

theorem SchW_mono_schemeD {n : Nat} {τ : Ty} (h : OkTD n τ) : SchWD n (mono τ) :=
  ⟨fun _ h => by simp [mono] at h, fun v hv _ => h v hv⟩

theorem find?_rsbVE (s : RSub) (VE : ValEnv) (x : String) :
    FMap.find? (rsbVE s VE) x = (FMap.find? VE x).map fun p => (rsbScheme s p.1, p.2) :=
  find?_mapVW (fun q : Scheme × IdStatus => (rsbScheme s q.1, q.2)) VE x

/-! ## Related contexts -/

theorem CtxRelD.plusVE {P : Scheme → Scheme → Prop} {R : RRigid} {C C' : Ctx} {VE VE' : ValEnv}
    (h : CtxRelD P R C C') (hVE : VEMatch P VE VE') : CtxRelD P R (C.plusVE VE) (C'.plusVE VE') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, hVE.append h5, h6⟩

theorem CtxRelD.mono {P Q : Scheme → Scheme → Prop} {R : RRigid} {C C' : Ctx} (h : CtxRelD P R C C')
    (hPQ : ∀ x σ st σ', FMap.find? C.E.VE x = some (σ, st) → P σ σ' → Q σ σ') : CtxRelD Q R C C' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun x => ?_, h6⟩
  have := h5 x
  revert this
  cases hf : FMap.find? C.E.VE x <;> cases FMap.find? C'.E.VE x <;> simp only [OptRel, imp_self]
  rename_i p p'
  exact fun ⟨e, hp⟩ => ⟨e, hPQ x p.1 p.2 p'.1 hf hp⟩

theorem vty_tyvars {w v : BVar} (h : v ∈ (vty w).tyvars) : v = w := by
  simp only [Ty.tyvars, List.mem_filter, vars_vty, List.mem_singleton] at h; exact h.1

/-- The free variables of `s C` are free in `C'`. -/
theorem CtxRelD.ftv {P : Scheme → Scheme → Prop} {R : RRigid} {s : RSub} {C C' : Ctx}
    (h : CtxRelD P R C C') (hP : ∀ σ σ', P σ σ' → FtvRelD s σ σ') (hs : FixR R s) :
    ∀ w ∈ C.tyvars, ∀ v ∈ (s.img w).tyvars, v ∈ C'.tyvars := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro w hw v hv
  rcases mem_ctx_tyvars.mp hw with hw | ⟨x, p, hf, hp⟩
  · rw [hs w (h6 w hw)] at hv
    rw [vty_tyvars hv]
    exact mem_ctx_tyvars.mpr (.inl (by simpa [restTv, h2, h3, h4] using hw))
  · have := h5 x
    rw [hf] at this
    revert this
    cases hf' : FMap.find? C'.E.VE x with
    | none => simp [OptRel]
    | some p' =>
      intro ⟨_, hpp⟩
      exact mem_ctx_tyvars.mpr (.inr ⟨x, p', hf', hP _ _ hpp w hp v hv⟩)

/-- A scheme is related to itself under a substitution fixing its free variables. -/
theorem schRel_reflD {s : RSub} {σ : Scheme}
    (hs : ∀ w ∈ σ.body.vars, w ∉ σ.bound → s.img w = vty w) : SchRelD s σ σ := by
  refine ⟨?_, ?_⟩
  · intro w hw v hv
    have hw' : w ∈ σ.body.vars ∧ w ∉ σ.bound := by
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not] at hw
      exact ⟨hw.1.1, hw.2⟩
    rw [hs w hw'.1 hw'.2] at hv
    rw [vty_tyvars hv]; exact hw
  · intro τ hg
    obtain ⟨g, hr, hout, rfl⟩ := gen_rsb hg
    refine ⟨g, fun a _ => hr a, rsb_congr _ fun w hw => ?_⟩
    rw [extS_img]
    split
    · rfl
    · rename_i hn; rw [hout w hn]; exact (hs w hw hn).symm

/-- The lookup clause of related contexts. -/
theorem CtxRelD.lookup {R : RRigid} {s : RSub} {C C' : Ctx} (h : CtxRelD (SchRelD s) R C C') (hs : FixR R s)
    (hRb : ∀ v : BVar, v.isBnd = true → R v = true)
    {lv : LongId} {σ' : Scheme} {st : IdStatus} (hl : C'.lookupVal lv = some (σ', st)) :
    ∃ σ, C.lookupVal lv = some (σ, st) ∧ SchRelD s σ σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl ⊢
    have := h5 lv.id
    rw [hl] at this
    revert this
    cases FMap.find? C.E.VE lv.id with
    | none => simp [OptRel]
    | some p => intro ⟨e, hp⟩; exact ⟨p.1, by cases p; simp_all, hp⟩
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl ⊢
    rw [h3]
    have qe_mem : ∀ w : BVar, w.isBnd = false → w ∈ σ'.body.vars → w ∉ σ'.bound → w ∈ restTv C := by
      intro w hwb hw hb
      cases hI : FMap.find? C'.E.QE m with
      | none => rw [hI] at hl; cases hl
      | some I =>
        rw [hI] at hl
        simp only [Option.bind_some] at hl
        simp only [restTv, List.mem_append]
        left; left
        rw [mem_tyvarsBy]
        refine ⟨m, I, by simp, by rw [h3]; exact hI, ?_⟩
        simp only [IEnv.tyvars, List.mem_append]
        right
        rw [mem_VE_tyvars]
        refine ⟨lv.id, (σ', st), hl, ?_⟩
        simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact ⟨⟨hw, hwb⟩, hb⟩
    refine ⟨σ', hl, schRel_reflD fun w hw hb => ?_⟩
    cases hwb : w.isBnd with
    | true => exact hs _ (hRb w hwb)
    | false => exact hs _ (h6 _ (qe_mem w hwb hw hb))

end StandardElm.Stat.Complete
