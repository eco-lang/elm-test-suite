/-
  A Standard Definition of Elm? Mechanisation: the closure at a `let` commutes with a later
  substitution of type and row variables that respects the closure's constraint (plan step 11,
  milestone (d), L10; WSoundClos.lean with rows).

  W closes `θ VE0` in `θ C`; the checker closes `s VE0` in `s C` (`s` absorbing `θ`). When `s`
  neither binds a generalised variable (type or row) nor puts one in the image of a free
  variable of `θ C` (`DeadC`), the generalised variables of the two closures are the same
  (`gen_iff`), they occur in the same order (`filter_rsb`: the merge of a substituted record's
  rows interleaves fields, but the fields a free tail brings have no generalised variable,
  `filter_mrg`), and so `s (Clos_{θ C} (θ VE0)) = Clos_{s C} (s VE0)` (`closGroup_rsb`), the
  canonical renaming read as a substitution (`canon_eqD`).
-/
import StandardElmMech.Stat.Complete.WDSoundBase

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

namespace WDS

/-! ## Order of first occurrences -/

theorem filter_rowVars_append (p : BVar → Bool) (l : Lab) (τ : Ty) (r : Row) :
    (Ty.rowVars ((l, τ) :: r)).filter p = τ.vars.filter p ++ (Ty.rowVars r).filter p := by
  simp [Ty.rowVars, List.filter_append]

/-- The merge interleaves; fields without a selected variable do not change the selection. -/
theorem filter_mrg (p : BVar → Bool) : ∀ (A X : Row), (∀ v ∈ Ty.rowVars X, p v = false) →
    (Ty.rowVars (mrg A X)).filter p = (Ty.rowVars A).filter p
  | [], X, h => by rw [mrg_nil_left, filter_nil_of h]; rfl
  | a :: A', [], _ => by rw [mrg_nil_right]
  | a :: A', x :: X', h => by
    rw [mrg_cons_cons]
    have hx : ∀ v ∈ x.2.vars, p v = false := fun v hv => h v (by simp [Ty.rowVars, hv])
    have hX' : ∀ v ∈ Ty.rowVars X', p v = false := fun v hv => h v (by simp [Ty.rowVars, hv])
    split
    · rw [filter_rowVars_append, filter_rowVars_append, filter_mrg p A' (x :: X') h]
    · rw [filter_rowVars_append, filter_mrg p (a :: A') X' hX', filter_nil_of hx, List.nil_append]
termination_by A X => A.length + X.length

/-- The hypothesis of `filter_rsb` for a variable. -/
def FilterOK (s : RSub) (p q : BVar → Bool) (a : BVar) : Prop :=
  (q a = true → s.img a = vty a ∧ p a = true) ∧ (q a = false → ∀ w ∈ (s.img a).vars, p w = false)

mutual
theorem filter_rsb (s : RSub) (p q : BVar → Bool) : ∀ τ : Ty, (∀ a ∈ τ.vars, FilterOK s p q a) →
    (rsb s τ).vars.filter p = τ.vars.filter q
  | .var a, h => by
    have ha := h (.ty a) (by simp [Ty.vars])
    show (s.img (.ty a)).vars.filter p = [BVar.ty a].filter q
    cases hq : q (.ty a)
    · rw [filter_nil_of (ha.2 hq)]; simp [hq]
    · obtain ⟨h1, h2⟩ := ha.1 hq
      rw [h1, vars_vty]; simp [hq, h2]
  | .record ρ none, h => by
    simp only [rsb, RSub.tl, mrg_nil_right]
    simp only [Ty.vars] at h ⊢
    exact filter_rsbRow s p q ρ h
  | .record ρ (some e), h => by
    simp only [rsb, RSub.tl]
    rw [vars_record]
    have hρ : ∀ a ∈ Ty.rowVars ρ, FilterOK s p q a := fun a ha => h a (by simp [Ty.vars, ha])
    have he := h (.row e) (by simp [Ty.vars])
    simp only [Ty.vars, List.filter_append]
    cases hq : q (.row e)
    · have hall : ∀ w ∈ (s.img (.row e)).vars, p w = false := he.2 hq
      simp only [RSub.img, vars_record] at hall
      rw [filter_mrg p _ _ (fun v hv => hall v (List.mem_append_left _ hv)),
        filter_nil_of (fun v hv => hall v (List.mem_append_right _ hv)), filter_rsbRow s p q ρ hρ]
      simp [hq]
    · obtain ⟨h1, h2⟩ := he.1 hq
      have hr : s.r e = ([], some e) := fix_row h1
      rw [hr]; simp only [mrg_nil_right, tailVars]
      rw [filter_rsbRow s p q ρ hρ]; simp [hq, h2]
  | .fn a b, h => by
    simp only [rsb, Ty.vars, List.filter_append] at h ⊢
    rw [filter_rsb s p q a (fun c hc => h c (List.mem_append_left _ hc)),
      filter_rsb s p q b (fun c hc => h c (List.mem_append_right _ hc))]
  | .con as _, h => by
    simp only [rsb, Ty.vars] at h ⊢
    exact filter_rsbList s p q as h
theorem filter_rsbRow (s : RSub) (p q : BVar → Bool) : ∀ ρ : Row, (∀ a ∈ Ty.rowVars ρ, FilterOK s p q a) →
    (Ty.rowVars (rsbRow s ρ)).filter p = (Ty.rowVars ρ).filter q
  | [], _ => rfl
  | (_, τ) :: rest, h => by
    simp only [rsbRow, Ty.rowVars, List.filter_append] at h ⊢
    rw [filter_rsb s p q τ (fun c hc => h c (List.mem_append_left _ hc)),
      filter_rsbRow s p q rest (fun c hc => h c (List.mem_append_right _ hc))]
theorem filter_rsbList (s : RSub) (p q : BVar → Bool) : ∀ l : List Ty, (∀ a ∈ Ty.listVars l, FilterOK s p q a) →
    (Ty.listVars (rsbList s l)).filter p = (Ty.listVars l).filter q
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [rsbList, Ty.listVars, List.filter_append] at h ⊢
    rw [filter_rsb s p q τ (fun c hc => h c (List.mem_append_left _ hc)),
      filter_rsbList s p q rest (fun c hc => h c (List.mem_append_right _ hc))]
end

/-! ## Free variables of a substituted context -/

theorem restTv_ctxRsb (u : RSub) (C : Ctx) : restTv (ctxRsb u C) = restTv C := rfl

theorem ctxRsb_tyvars_mem {u : RSub} {C : Ctx} (hb : ∀ v, v.isBnd = true → u.img v = vty v)
    (hC : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true)
    {w : BVar} (h : w ∈ (ctxRsb u C).tyvars) :
    w ∈ restTv C ∨ ∃ x p e, FMap.find? C.E.VE x = some p ∧ e ∈ p.1.body.vars ∧ e ∉ p.1.bound ∧ w ∈ (u.img e).vars := by
  rcases mem_ctx_tyvars.mp h with h | ⟨x, p', hf, hp⟩
  · exact .inl h
  · change FMap.find? (rsbVE u C.E.VE) x = some p' at hf
    rw [find?_rsbVE] at hf
    cases hq : FMap.find? C.E.VE x with
    | none => rw [hq] at hf; cases hf
    | some p =>
      rw [hq] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
      obtain ⟨h1, h2, h3⟩ := mem_scheme_tyvars.mp hp
      simp only [rsbScheme] at h1 h3
      obtain ⟨e, he, hwe⟩ := (mem_vars_rsb _ _ w).mp h1
      refine .inr ⟨x, p, e, hq, he, fun hm => ?_, hwe⟩
      rw [hb e (hC x p hq e hm), vars_vty, List.mem_singleton] at hwe; subst hwe
      exact h3 hm

theorem ctxRsb_tyvars_of {u : RSub} {C : Ctx}
    (hC : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true)
    {w : BVar} (hw : w.isBnd = false) {x : String} {p : Scheme × IdStatus} {e : BVar}
    (hf : FMap.find? C.E.VE x = some p) (he : e ∈ p.1.body.vars) (hwe : w ∈ (u.img e).vars) :
    w ∈ (ctxRsb u C).tyvars := by
  refine mem_ctx_tyvars.mpr (.inr ⟨x, (rsbScheme u p.1, p.2), by
    change FMap.find? (rsbVE u C.E.VE) x = _; rw [find?_rsbVE, hf]; rfl, ?_⟩)
  refine mem_scheme_tyvars.mpr ⟨vars_rsb_of he hwe, hw, fun hm => ?_⟩
  rw [hC x p hf w hm] at hw; cases hw

/-! ## The hypotheses of the commutation -/

structure ClosHypD (n0 : Nat) (C : Ctx) (VE0 : ValEnv) (θ s : RSub) : Prop where
  isMono : ∀ q ∈ VE0, q.2.1.bound = []
  ok : ∀ q ∈ VE0, ∀ v ∈ q.2.1.body.vars, v.isBnd = false
  θok : SOk n0 θ
  idem : IdemS θ
  sok : SOk n0 s
  abs : AbsS s θ
  dead : DeadC ((ctxRsb θ C).tyvars, veBodies (rsbVE θ VE0)) s
  ctxB : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true
  ctxF : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.body.vars, v ∉ p.1.bound → v.isBnd = false
  rest : ∀ v ∈ restTv C, rigidFromD n0 v = true

theorem SOk.bnd {n0 : Nat} {s : RSub} (h : SOk n0 s) {v : BVar} (hv : v.isBnd = true) : s.img v = vty v :=
  h.fix v (rigidFromD_bnd n0 hv)

theorem SOk.vars {n0 : Nat} {s : RSub} (h : SOk n0 s) {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isBnd = false) :
    ∀ v ∈ (rsb s τ).vars, v.isBnd = false := by
  intro v hv
  obtain ⟨e, he, hve⟩ := (mem_vars_rsb _ _ v).mp hv
  exact h.img e (hτ e he) v hve

theorem mem_veBodies_rsb {u : RSub} {VE0 : ValEnv} {τ : Ty} (hτ : τ ∈ veBodies VE0) :
    rsb u τ ∈ veBodies (rsbVE u VE0) := by
  simp only [veBodies, rsbVE, List.mem_map] at hτ ⊢
  obtain ⟨q, hq, rfl⟩ := hτ
  exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩

theorem mem_VE_tyvars_rsb {u : RSub} {VE0 : ValEnv} {v : BVar} (h : v ∈ (rsbVE u VE0).tyvars) :
    ∃ τ ∈ veBodies VE0, v ∈ (rsb u τ).vars := by
  obtain ⟨x, p, hf, hp⟩ := mem_VE_tyvars.mp h
  rw [find?_rsbVE] at hf
  cases hq : FMap.find? VE0 x with
  | none => rw [hq] at hf; cases hf
  | some q =>
    rw [hq] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
    exact ⟨q.1.body, List.mem_map.mpr ⟨(x, q), find?_mem hq, rfl⟩, (mem_scheme_tyvars.mp hp).1⟩

section
variable {n0 : Nat} {C : Ctx} {VE0 : ValEnv} {θ s : RSub} (H : ClosHypD n0 C VE0 θ s)
include H

theorem ClosHypD.okθ {τ : Ty} (hτ : τ ∈ veBodies VE0) : ∀ v ∈ (rsb θ τ).vars, v.isBnd = false := by
  simp only [veBodies, List.mem_map] at hτ
  obtain ⟨q, hq, rfl⟩ := hτ
  exact H.θok.vars (H.ok q hq)

/-- A variable of the image under `θ` of a free variable of `C`: free in `θ C`. -/
theorem ClosHypD.inA {e : BVar} (he : e.isBnd = false) {x : String} {p : Scheme × IdStatus} {e' : BVar}
    (hf : FMap.find? C.E.VE x = some p) (he' : e' ∈ p.1.body.vars) (hee : e ∈ (θ.img e').vars) :
    e ∈ (ctxRsb θ C).tyvars :=
  ctxRsb_tyvars_of H.ctxB he hf he' hee

/-- A variable of a group type under `θ`: generalised, or free in `θ C`. -/
theorem ClosHypD.gen_or {τ : Ty} (hτ : τ ∈ veBodies VE0) {e : BVar} (he : e ∈ (rsb θ τ).vars) :
    InG ((ctxRsb θ C).tyvars, veBodies (rsbVE θ VE0)) e ∨ e ∈ (ctxRsb θ C).tyvars :=
  if h : e ∈ (ctxRsb θ C).tyvars then .inr h else .inl ⟨⟨_, mem_veBodies_rsb hτ, he⟩, h⟩

/-- The image under `s` of a variable free in `θ C`: free in `s C`, without a generalised variable. -/
theorem ClosHypD.freeImg {e w : BVar} (he : e ∈ (ctxRsb θ C).tyvars) (hw : w ∈ (s.img e).vars) :
    w ∈ (ctxRsb s C).tyvars ∧ ¬ InG ((ctxRsb θ C).tyvars, veBodies (rsbVE θ VE0)) w := by
  refine ⟨?_, fun hg => (H.dead w hg).2 e he hw⟩
  rcases ctxRsb_tyvars_mem (fun v hv => H.θok.bnd hv) H.ctxB he with hr | ⟨x, p, e', hf, he', hnb, hee⟩
  · rw [H.sok.fix e (H.rest e hr), vars_vty, List.mem_singleton] at hw; subst hw
    exact mem_ctx_tyvars.mpr (.inl hr)
  · have hw' : w ∈ (s.img e').vars := by rw [← H.abs e']; exact vars_rsb_of hee hw
    have hwB : w.isBnd = false := H.sok.img e' (H.ctxF x p hf e' he' hnb) w hw'
    exact ctxRsb_tyvars_of H.ctxB hwB hf he' hw'

end

section
variable {n0 : Nat} {C : Ctx} {VE0 : ValEnv} {θ s : RSub} (H : ClosHypD n0 C VE0 θ s)
include H

/-- The generalised variables of the checker's closure are those of W's closure. -/
theorem ClosHypD.gen_iff {τ : Ty} (hτ : τ ∈ veBodies VE0) {w : BVar} (hw : w ∈ (rsb s τ).vars) :
    w ∉ (ctxRsb s C).tyvars ↔ InG ((ctxRsb θ C).tyvars, veBodies (rsbVE θ VE0)) w := by
  rw [← absS_rsb H.abs] at hw
  obtain ⟨e, he, hwe⟩ := (mem_vars_rsb _ _ w).mp hw
  constructor
  · intro hn
    rcases H.gen_or hτ he with hg | hA
    · rw [(H.dead e hg).1, vars_vty, List.mem_singleton] at hwe; subst hwe; exact hg
    · exact absurd (H.freeImg hA hwe).1 hn
  · intro hg hm
    rcases ctxRsb_tyvars_mem (fun v hv => H.sok.bnd hv) H.ctxB hm with hr | ⟨x, p, e', hf, he', hnb, hee⟩
    · exact hg.2 (mem_ctx_tyvars.mpr (.inl (by rw [restTv_ctxRsb]; exact hr)))
    · rw [← H.abs e'] at hee
      obtain ⟨e'', he'', hwe''⟩ := (mem_vars_rsb _ _ w).mp hee
      have hB : e''.isBnd = false := H.θok.img e' (H.ctxF x p hf e' he' hnb) e'' he''
      exact (H.dead w hg).2 e'' (H.inA hB hf he' he'') hwe''

/-- A generalised variable is in the image under `s` exactly when it is in the image under `θ`. -/
theorem ClosHypD.occS {τ : Ty} (hτ : τ ∈ veBodies VE0) {b : BVar}
    (hg : InG ((ctxRsb θ C).tyvars, veBodies (rsbVE θ VE0)) b) :
    b ∈ (rsb s (rsb θ τ)).vars ↔ b ∈ (rsb θ τ).vars := by
  constructor
  · intro hb
    obtain ⟨c, hc, hbc⟩ := (mem_vars_rsb _ _ b).mp hb
    rcases H.gen_or hτ hc with hcg | hcA
    · rw [(H.dead c hcg).1, vars_vty, List.mem_singleton] at hbc; subst hbc; exact hc
    · exact absurd hbc ((H.dead b hg).2 c hcA)
  · intro hb; exact vars_rsb_of hb (by rw [(H.dead b hg).1, vars_vty]; exact List.mem_singleton_self _)

end

theorem extraEqD (A : List BVar) (VE : ValEnv) (τ' : Ty) :
    ((diffL (dedupL (ValEnv.tyvars VE)) (τ'.tyvars ++ A)).filter BVar.isNumTyVar) =
      dedupL ((ValEnv.tyvars VE).filter fun v => v.isNumTyVar && !decide (v ∈ τ'.tyvars) && !decide (v ∈ A)) := by
  simp only [diffL]
  rw [List.filter_filter, filter_dedupL]
  congr 1
  apply List.filter_congr
  intro v _
  simp only [List.mem_append]
  cases v.isNumTyVar <;> by_cases h1 : v ∈ τ'.tyvars <;> by_cases h2 : v ∈ A <;> simp [h1, h2]

theorem mem_closB {A : List BVar} {VE : ValEnv} {τ : Ty} {v : BVar} :
    v ∈ closB A VE (mono τ) ↔ (v ∈ τ.tyvars ∧ v ∉ A) ∨
      ((v ∈ ValEnv.tyvars VE ∧ v ∉ τ.tyvars ∧ v ∉ A) ∧ v.isNumTyVar = true) := by
  simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
    decide_eq_false_iff_not, Bool.not_eq_true', not_or]

section
variable {n0 : Nat} {C : Ctx} {VE0 : ValEnv} {θ s : RSub} (H : ClosHypD n0 C VE0 θ s)
include H

theorem ClosHypD.member {τ : Ty} (hτ : τ ∈ veBodies VE0) :
    rsbScheme s (closE (ctxRsb θ C).tyvars (rsbVE θ VE0) (mono (rsb θ τ))) =
      closE (ctxRsb s C).tyvars (rsbVE s VE0) (mono (rsb s τ)) := by
  have okτ : ∀ v ∈ τ.vars, v.isBnd = false := by
    simp only [veBodies, List.mem_map] at hτ; obtain ⟨q, hq, rfl⟩ := hτ; exact H.ok q hq
  have ok1 := H.okθ hτ
  have okS := H.sok.vars okτ
  have hsτ : rsb s τ = rsb s (rsb θ τ) := (absS_rsb H.abs τ).symm
  have hL := mem_veBodies_rsb (u := θ) hτ
  generalize hAL : (ctxRsb θ C).tyvars = AL at *
  generalize hAR : (ctxRsb s C).tyvars = AR at *
  have tyv : ∀ {σ : Ty} {v : BVar}, (∀ w ∈ σ.vars, w.isBnd = false) → (v ∈ σ.tyvars ↔ v ∈ σ.vars) :=
    fun hσ => by rw [mem_tyvars_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hσ _ h⟩⟩
  -- the generalised variables, on each side
  have inGL : ∀ c ∈ closB AL (rsbVE θ VE0) (mono (rsb θ τ)), InG (AL, veBodies (rsbVE θ VE0)) c := by
    intro c hc
    rcases mem_closB.mp hc with ⟨h1, h2⟩ | ⟨⟨h1, -, h2⟩, -⟩
    · exact ⟨⟨_, hL, (mem_tyvars_iff.mp h1).1⟩, h2⟩
    · obtain ⟨τ', hτ', hv'⟩ := mem_VE_tyvars_rsb h1
      exact ⟨⟨_, mem_veBodies_rsb hτ', hv'⟩, h2⟩
  have memL : ∀ a ∈ (rsb θ τ).vars, a ∈ closB AL (rsbVE θ VE0) (mono (rsb θ τ)) ↔
      InG (AL, veBodies (rsbVE θ VE0)) a := fun a ha =>
    ⟨inGL a, fun hg => mem_closB.mpr (.inl ⟨(tyv ok1).mpr ha, hg.2⟩)⟩
  have genAny : ∀ {τ' : Ty}, τ' ∈ veBodies VE0 → ∀ w ∈ (rsb s τ').vars, w ∉ AR ↔ InG (AL, veBodies (rsbVE θ VE0)) w := by
    intro τ' hτ' w hw; have := H.gen_iff hτ' hw; rwa [hAL, hAR] at this
  have genR := genAny hτ
  have memR : ∀ w ∈ (rsb s τ).vars, w ∈ closB AR (rsbVE s VE0) (mono (rsb s τ)) ↔
      InG (AL, veBodies (rsbVE θ VE0)) w := by
    intro w hw
    rw [← genR w hw, mem_closB]
    constructor
    · rintro (⟨_, h⟩ | ⟨⟨_, h, _⟩, _⟩)
      · exact h
      · exact absurd ((tyv okS).mpr hw) h
    · intro h; exact .inl ⟨(tyv okS).mpr hw, h⟩
  have occ : ∀ {τ' : Ty}, τ' ∈ veBodies VE0 → ∀ b, InG (AL, veBodies (rsbVE θ VE0)) b →
      (b ∈ (rsb s (rsb θ τ')).vars ↔ b ∈ (rsb θ τ').vars) := fun hτ' b hb => by
    have := H.occS hτ' (b := b); rw [hAL] at this; exact this hb
  have deadA : ∀ a ∈ AL, ∀ w ∈ (s.img a).vars, ¬ InG (AL, veBodies (rsbVE θ VE0)) w := fun a ha w hw hg => by
    have := (H.dead w (by rw [hAL]; exact hg)).2 a (by rw [hAL]; exact ha); exact this hw
  have fixG : ∀ b, InG (AL, veBodies (rsbVE θ VE0)) b → s.img b = vty b := fun b hb =>
    (H.dead b (by rw [hAL]; exact hb)).1
  have genOr : ∀ {τ' : Ty}, τ' ∈ veBodies VE0 → ∀ e ∈ (rsb θ τ').vars, InG (AL, veBodies (rsbVE θ VE0)) e ∨ e ∈ AL :=
    fun hτ' e he => by have := H.gen_or hτ' he; rwa [hAL] at this
  -- the occurring bound variables, in order
  have hocc : (rsb s τ).vars.filter (fun v => decide (v ∈ closB AR (rsbVE s VE0) (mono (rsb s τ)))) =
      (rsb θ τ).vars.filter (fun v => decide (v ∈ closB AL (rsbVE θ VE0) (mono (rsb θ τ)))) := by
    rw [hsτ]
    apply filter_rsb
    intro a ha
    refine ⟨fun hq => ?_, fun hq w hw => ?_⟩
    · have hg := (memL a ha).mp (by simpa using hq)
      refine ⟨fixG a hg, ?_⟩
      have hw : a ∈ (rsb s τ).vars := by rw [hsτ]; exact vars_rsb_of ha (by rw [fixG a hg, vars_vty]; simp)
      rw [← hsτ]; simpa using (memR a hw).mpr hg
    · have hng : ¬ InG (AL, veBodies (rsbVE θ VE0)) a := fun hg => by
        have := (memL a ha).mpr hg; simp [this] at hq
      have haA : a ∈ AL := (genOr hτ a ha).resolve_left hng
      have hw' : w ∈ (rsb s τ).vars := by rw [hsτ]; exact vars_rsb_of ha hw
      rw [← hsτ]
      cases hm : decide (w ∈ closB AR (rsbVE s VE0) (mono (rsb s τ)))
      · exact hm
      · exact absurd ((memR w hw').mp (by simpa using hm)) (deadA a haA w hw)
  -- the number variables of the group's environment that are generalised (A93)
  have hX : (ValEnv.tyvars (rsbVE s VE0)).filter (fun v => v.isNumTyVar && !decide (v ∈ (rsb s τ).tyvars) &&
        !decide (v ∈ AR)) =
      (ValEnv.tyvars (rsbVE θ VE0)).filter (fun v => v.isNumTyVar && !decide (v ∈ (rsb θ τ).tyvars) &&
        !decide (v ∈ AL)) := by
    show (FMap.tyvarsBy (fun b => b.1.tyvars) [] (rsbVE s VE0)).filter _ =
      (FMap.tyvarsBy (fun b => b.1.tyvars) [] (rsbVE θ VE0)).filter _
    have e1 : rsbVE s VE0 = (rsbVE θ VE0).map fun e => (e.1, (rsbScheme s e.2.1, e.2.2)) := by
      rw [show (rsbVE θ VE0).map (fun e => (e.1, (rsbScheme s e.2.1, e.2.2))) = rsbVE s (rsbVE θ VE0) from rfl,
        rsbVE_sbD, absS_comp H.abs]
    rw [e1]
    refine filter_tyvarsBy (rsbVE θ VE0) (fun e => (rsbScheme s e.1, e.2)) [] fun e he => ?_
    simp only [rsbVE, List.mem_map] at he
    obtain ⟨q, hq, rfl⟩ := he
    have hτq : q.2.1.body ∈ veBodies VE0 := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hmq : q.2.1 = mono q.2.1.body := by
      have hb := H.isMono q hq; revert hb; obtain ⟨_, ⟨b, body⟩, _⟩ := q; intro hb; simp only at hb; subst hb; rfl
    dsimp only
    rw [hmq, rsbScheme_monoD, rsbScheme_monoD, mono_tyvars, mono_tyvars]
    generalize hTR : (rsb s τ).tyvars = TR
    generalize hTL : (rsb θ τ).tyvars = TL
    simp only [Ty.tyvars, List.filter_filter]
    have okq := H.okθ hτq
    apply filter_rsb
    intro a ha
    have haB := okq a ha
    have hτR : ∀ v, v ∈ TR ↔ v ∈ (rsb s τ).vars := fun v => hTR ▸ tyv okS
    have hτL : ∀ v, v ∈ TL ↔ v ∈ (rsb θ τ).vars := fun v => hTL ▸ tyv ok1
    refine ⟨fun hq' => ?_, fun hq' w hw => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq'
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hq'
      have h2' : a ∉ TL := of_decide_eq_false h2
      have h3' : a ∉ AL := of_decide_eq_false h3
      have hg : InG (AL, veBodies (rsbVE θ VE0)) a := ⟨⟨_, mem_veBodies_rsb hτq, ha⟩, h3'⟩
      refine ⟨fixG a hg, ?_⟩
      have haR : a ∈ (rsb s q.2.1.body).vars := by
        rw [← absS_rsb H.abs]; exact vars_rsb_of ha (by rw [fixG a hg, vars_vty]; simp)
      have hnR : a ∉ AR := (genAny hτq a haR).mpr hg
      have hnτ : a ∉ TR := fun h => h2' ((hτL a).mpr (by
        rw [hτR, hsτ] at h; exact (occ hτ a hg).mp h))
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨⟨h1, decide_eq_false hnτ⟩, decide_eq_false hnR⟩, by simp [haB]⟩
    · have hwB : w.isBnd = false := H.sok.img a haB w hw
      rcases genOr hτq a ha with hg | haA
      · rw [fixG a hg, vars_vty, List.mem_singleton] at hw; subst hw
        by_cases hn : w.isNumTyVar = true
        · by_cases hτa : w ∈ TL
          · have : w ∈ TR := (hτR w).mpr (by rw [hsτ]; exact (occ hτ w hg).mpr ((hτL w).mp hτa))
            simp [this]
          · exfalso; simp [hn, hτa, hg.2, haB] at hq'
        · simp [hn]
      · have hwA : w ∈ AR := by have := (H.freeImg (by rw [hAL]; exact haA) hw).1; rwa [hAR] at this
        simp [hwA]
  -- the canonical orders agree
  have hcv : canonVars (closB AR (rsbVE s VE0) (mono (rsb s τ))) (rsb s τ) =
      canonVars (closB AL (rsbVE θ VE0) (mono (rsb θ τ))) (rsb θ τ) := by
    unfold canonVars
    dsimp only
    rw [hocc]
    congr 2
    generalize hO : dedupL ((rsb θ τ).vars.filter fun v => decide (v ∈ closB AL (rsbVE θ VE0) (mono (rsb θ τ)))) = O
    have hOsub : ∀ v ∈ O, v ∈ (rsb θ τ).vars ∧ InG (AL, veBodies (rsbVE θ VE0)) v := by
      rw [← hO]; intro v hv
      rw [mem_dedupL, List.mem_filter] at hv
      exact ⟨hv.1, inGL v (by simpa using hv.2)⟩
    have split : ∀ (A : List BVar) (VE : ValEnv) (τ' : Ty), (∀ v ∈ τ'.vars, v ∉ A → v ∈ O) →
        (∀ v ∈ O, v ∈ τ'.vars) → (∀ v ∈ τ'.vars, v.isBnd = false) →
        (closB A VE (mono τ')).filter (fun v => v.isNumTyVar && !decide (v ∈ O)) =
          (diffL (dedupL (ValEnv.tyvars VE)) (τ'.tyvars ++ A)).filter BVar.isNumTyVar := by
      intro A VE τ' h1 h2 h3
      simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.filter_append]
      rw [filter_nil_of (l := diffL (dedupL τ'.tyvars) A) fun v hv => by
        simp only [diffL, List.mem_filter, mem_dedupL, Bool.not_eq_true', decide_eq_false_iff_not] at hv
        have := h1 v (mem_tyvars_iff.mp hv.1).1 hv.2
        simp [this], List.nil_append, List.filter_filter]
      apply List.filter_congr
      intro v hv
      have hv1 : v ∉ τ'.tyvars := by
        intro h
        simp only [diffL, List.mem_filter, List.mem_append, Bool.not_eq_true', decide_eq_false_iff_not] at hv
        exact hv.2 (.inl h)
      have hvO : v ∉ O := fun hm => hv1 (mem_tyvars_iff.mpr ⟨h2 v hm, h3 v (h2 v hm)⟩)
      simp [hvO]
    rw [split AR (rsbVE s VE0) (rsb s τ) (fun v hv hvA => by
        have hg := (genR v hv).mp hvA
        have hvL : v ∈ (rsb θ τ).vars := by rw [hsτ] at hv; exact (occ hτ v hg).mp hv
        rw [← hO]; exact mem_dedupL.mpr (List.mem_filter.mpr ⟨hvL, by simpa using (memL v hvL).mpr hg⟩))
      (fun v hv => by rw [hsτ]; exact (occ hτ v (hOsub v hv).2).mpr (hOsub v hv).1) okS,
      split AL (rsbVE θ VE0) (rsb θ τ) (fun v hv hvA => by
        rw [← hO]; exact mem_dedupL.mpr (List.mem_filter.mpr ⟨hv, by simpa using (memL v hv).mpr ⟨⟨_, hL, hv⟩, hvA⟩⟩))
        (fun v hv => (hOsub v hv).1) ok1,
      extraEqD, extraEqD, hX]
  -- the closures, read as renamings
  unfold closE
  rw [mono_body, mono_body, canon_eqD, canon_eqD, hcv]
  simp only [rsbScheme, Scheme.mk.injEq, true_and]
  rw [hsτ, rsb_rsb _ s (rsb θ τ), rsb_rsb s _ (rsb θ τ)]
  apply rsb_congr
  intro v hv
  rw [img_rcomp, img_rcomp, renumber_img]
  split
  · rename_i hm
    have hg := inGL v (mem_canonVars hm)
    rw [rsb_vty, H.sok.bnd (bndV_isBnd _ _), fixG v hg, rsb_vty, renumber_img, if_pos hm]
  · rename_i hm
    rw [rsb_vty]
    symm
    refine rsb_eq_self fun w hw => ?_
    rw [renumber_img, if_neg]
    intro hw'
    have hng : ¬ InG (AL, veBodies (rsbVE θ VE0)) v := fun hg =>
      hm ((mem_canonVars_iff hv).mpr ((memL v hv).mpr hg))
    have hvA : v ∈ AL := (genOr hτ v hv).resolve_left hng
    exact deadA v hvA w hw (inGL w (mem_canonVars hw'))

/-- The closure at a `let` commutes with a later substitution respecting its constraint. -/
theorem closGroup_rsb :
    rsbVE s (closGroup (ctxRsb θ C).tyvars (rsbVE θ VE0)) = closGroup (ctxRsb s C).tyvars (rsbVE s VE0) := by
  rw [closGroup_eq, closGroup_eq]
  simp only [rsbVE, FMap.mapV, List.map_map]
  apply List.map_congr_left
  intro q hq
  obtain ⟨x, ⟨bd, τ⟩, st⟩ := q
  have hb : bd = [] := H.isMono _ hq
  subst hb
  have hτ : τ ∈ veBodies VE0 := List.mem_map.mpr ⟨_, hq, rfl⟩
  simp only [Function.comp, Prod.mk.injEq, true_and, and_true]
  exact H.member hτ

end

end WDS

end StandardElm.Stat.Complete
