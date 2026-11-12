/-
  A Standard Definition of Elm? Mechanisation: the closure at a `let` commutes with a later
  substitution that respects the closure's constraint (plan step 11, milestone (b), L10).

  W closes the group's environment `θ VE0` in the context `θ C` (`θ` the substitution after the
  group); the checker closes `s VE0` in `s C` (`s` the final substitution, absorbing `θ`). When
  `s` neither binds a generalised variable nor puts one in the image of a free variable of
  `θ C` (`DeadC`), the generalised variables of the two closures are the same (`gen_iff`), they
  occur in the same order (`filter_sb`), and so `s (Clos_{θ C} (θ VE0)) = Clos_{s C} (s VE0)`
  (`closGroup_sb`), canonical forms included.
-/
import StandardElmMech.Stat.Complete.WSoundPost

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Free variables of a substituted context -/

theorem restTv_ctxSb (u : FSub) (C : Ctx) : restTv (ctxSb u C) = restTv C := rfl

theorem ctxSb_tyvars_mem {u : FSub} {C : Ctx} (hb : ∀ i c, u (.bnd i c) = .var (.bnd i c))
    (hC : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true)
    {w : BVar} (h : w ∈ (ctxSb u C).tyvars) :
    w ∈ restTv C ∨ (∃ x p e, FMap.find? C.E.VE x = some p ∧ TV e p.1.body ∧ BVar.ty e ∉ p.1.bound ∧ w ∈ (u e).vars) ∨
      (∃ x p, FMap.find? C.E.VE x = some p ∧ w ∈ p.1.body.vars ∧ (∃ r, w = .row r)) := by
  rcases mem_ctx_tyvars.mp h with h | ⟨x, p', hf, hp⟩
  · exact .inl h
  · change FMap.find? (sbVE u C.E.VE) x = some p' at hf
    rw [find?_sbVE] at hf
    cases hq : FMap.find? C.E.VE x with
    | none => rw [hq] at hf; cases hf
    | some p =>
      rw [hq] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
      obtain ⟨h1, h2, h3⟩ := mem_scheme_tyvars.mp hp
      simp only [sbScheme] at h1 h3
      rcases vars_sb u _ w h1 with ⟨r, rfl, hr⟩ | ⟨e, he, hwe⟩
      · exact .inr (.inr ⟨x, p, hq, hr, r, rfl⟩)
      · refine .inr (.inl ⟨x, p, e, hq, he, fun hm => ?_, hwe⟩)
        have hbe := hC x p hq _ hm
        cases e with
        | bnd i c =>
          rw [hb i c] at hwe
          simp only [Ty.vars, List.mem_singleton] at hwe; subst hwe; simp [BVar.isBnd] at h2
        | _ => simp [BVar.isBnd] at hbe

theorem ctxSb_tyvars_of {u : FSub} {C : Ctx}
    (hC : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true)
    {w : BVar} (hw : w.isBnd = false) {x : String} {p : Scheme × IdStatus} {e : TyVar}
    (hf : FMap.find? C.E.VE x = some p) (he : TV e p.1.body) (hwe : w ∈ (u e).vars) : w ∈ (ctxSb u C).tyvars := by
  refine mem_ctx_tyvars.mpr (.inr ⟨x, (sbScheme u p.1, p.2), by change FMap.find? (sbVE u C.E.VE) x = _; rw [find?_sbVE, hf]; rfl, ?_⟩)
  refine mem_scheme_tyvars.mpr ⟨vars_sb_of _ _ e w he hwe, hw, fun hm => ?_⟩
  rw [hC x p hf w hm] at hw; cases hw

/-! ## The generalised variables of the two closures -/

/-- The hypotheses of the commutation, for W's context `C`, the group environment `VE0`, the
    substitution `θ` at the closure and a later `s`. -/
structure ClosHyp (n0 : Nat) (C : Ctx) (VE0 : ValEnv) (θ s : FSub) : Prop where
  isMono : ∀ q ∈ VE0, q.2.1.bound = []
  ok : ∀ q ∈ VE0, ∀ v ∈ q.2.1.body.vars, ∃ a, v = .ty a ∧ a.isBndT = false
  θok : SOk n0 θ
  idem : Idem θ
  sok : SOk n0 s
  abs : Absorbs s θ
  dead : DeadC ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) s
  ctxB : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true
  ctxF : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.body.vars, v ∉ p.1.bound →
    ∃ a, v = .ty a ∧ a.isBndT = false
  rest : ∀ a, BVar.ty a ∈ restTv C → rigidFrom n0 a = true

theorem rigid_bnd' (n0 i : Nat) (c : Cls) : rigidFrom n0 (.bnd i c) = true := rfl

theorem SOk.bnd {n0 : Nat} {s : FSub} (h : SOk n0 s) (i : Nat) (c : Cls) : s (.bnd i c) = .var (.bnd i c) :=
  h.1 _ (rigid_bnd' n0 i c)

/-- The image of a type W built under a substitution of `SOk`: type variables, not `bnd`. -/
theorem SOk.vars {n0 : Nat} {s : FSub} (h : SOk n0 s) {τ : Ty} (hτ : ∀ v ∈ τ.vars, ∃ a, v = .ty a ∧ a.isBndT = false) :
    ∀ v ∈ (sb s τ).vars, ∃ a, v = .ty a ∧ a.isBndT = false := by
  intro v hv
  rcases vars_sb s τ v hv with ⟨r, rfl, hr⟩ | ⟨e, he, hve⟩
  · obtain ⟨a, e, _⟩ := hτ _ hr; cases e
  · obtain ⟨a, e', hab⟩ := hτ _ he
    injection e' with e'; subst e'
    exact h.2 e hab v hve

section
variable {n0 : Nat} {C : Ctx} {VE0 : ValEnv} {θ s : FSub} (H : ClosHyp n0 C VE0 θ s)
include H

theorem ClosHyp.okθ {τ : Ty} (hτ : τ ∈ veBodies VE0) : ∀ v ∈ (sb θ τ).vars, ∃ a, v = .ty a ∧ a.isBndT = false := by
  simp only [veBodies, List.mem_map] at hτ
  obtain ⟨q, hq, rfl⟩ := hτ
  exact H.θok.vars (H.ok q hq)

omit H in
theorem ClosHyp.mem_L {τ : Ty} (hτ : τ ∈ veBodies VE0) : sb θ τ ∈ veBodies (sbVE θ VE0) := by
  simp only [veBodies, List.mem_map] at hτ ⊢
  obtain ⟨q, hq, rfl⟩ := hτ
  exact ⟨_, List.mem_map_of_mem hq, rfl⟩

/-- A free variable of `θ C`: in `θ C` exactly. -/
theorem ClosHyp.inA {e : TyVar} (he : e.isBndT = false) {x : String} {p : Scheme × IdStatus} {e' : TyVar}
    (hf : FMap.find? C.E.VE x = some p) (he' : TV e' p.1.body) (hee : TV e (θ e')) :
    BVar.ty e ∈ (ctxSb θ C).tyvars :=
  ctxSb_tyvars_of H.ctxB (by simp [BVar.isBnd]; cases e <;> simp_all [TyVar.isBndT]) hf he' hee

/-- The generalised variables of the checker's closure are those of W's closure. -/
theorem ClosHyp.gen_iff {τ : Ty} (hτ : τ ∈ veBodies VE0) {w : BVar} (hw : w ∈ (sb s τ).vars) :
    w ∉ (ctxSb s C).tyvars ↔ ∃ b, w = .ty b ∧ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b := by
  rw [← absorbs_sb' H.abs] at hw
  obtain ⟨b, rfl, hbb⟩ := H.sok.vars (H.okθ hτ) w hw
  obtain ⟨e, he, hbe⟩ := tyvar_sb hw
  obtain ⟨e0, ee, heb⟩ := H.okθ hτ _ he
  injection ee with ee; subst ee
  have hbB : (BVar.ty b).isBnd = false := by simp [BVar.isBnd]; cases b <;> simp_all [TyVar.isBndT]
  constructor
  · intro hn
    refine ⟨b, rfl, ?_⟩
    by_cases hg : InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) e
    · rw [(H.dead e hg).1] at hbe
      simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hbe; subst hbe; exact hg
    · exfalso
      have heA : BVar.ty e ∈ (ctxSb θ C).tyvars := by
        refine Classical.byContradiction fun h => hg ⟨⟨_, ClosHyp.mem_L (θ := θ) hτ, he⟩, h⟩
      rcases ctxSb_tyvars_mem (fun i c => H.θok.bnd i c) H.ctxB heA with hr | ⟨x, p, e', hf, he', hnb, hee⟩ | ⟨_, _, _, _, r, hr⟩
      · rw [H.sok.1 _ (H.rest e hr)] at hbe
        simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hbe; subst hbe
        exact hn (mem_ctx_tyvars.mpr (.inl hr))
      · have : TV b (s e') := by rw [← H.abs e']; exact vars_sb_of _ _ e _ hee hbe
        exact hn (ctxSb_tyvars_of H.ctxB hbB hf he' this)
      · cases hr
  · rintro ⟨b', e1, hg⟩ hm
    injection e1 with e1; subst e1
    rcases ctxSb_tyvars_mem (fun i c => H.sok.bnd i c) H.ctxB hm with hr | ⟨x, p, e', hf, he', hnb, hee⟩ | ⟨_, _, _, _, r, hr⟩
    · exact hg.2 (mem_ctx_tyvars.mpr (.inl hr))
    · rw [← H.abs e'] at hee
      obtain ⟨e'', he'', hbe''⟩ := tyvar_sb hee
      obtain ⟨a, ea, hab⟩ := H.ctxF x p hf _ he' hnb
      injection ea with ea; subst ea
      have he''b : e''.isBndT = false := by
        by_cases h0 : θ e' = .var e'
        · rw [h0] at he''; simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at he''; subst he''; exact hab
        · obtain ⟨c, ec, hc⟩ := H.θok.2 e' hab _ he''
          injection ec with ec; subst ec; exact hc
      exact (H.dead b hg).2 e'' (H.inA he''b hf he' he'') hbe''
    · cases hr

end

/-! ## Order of first occurrences -/

mutual
theorem filter_sb (s : FSub) (p q : BVar → Bool) : ∀ τ : Ty, (∀ v ∈ τ.vars, ∃ a, v = .ty a) →
    (∀ a, TV a τ → (q (.ty a) = true → s a = .var a ∧ p (.ty a) = true) ∧
      (q (.ty a) = false → ∀ w ∈ (s a).vars, p w = false)) →
    (sb s τ).vars.filter p = τ.vars.filter q
  | .var a, _, h => by
    simp only [sb, Ty.vars]
    cases hq : q (.ty a)
    · rw [List.filter_eq_nil_iff.mpr fun w hw => by simp [(h a (mem_vars_var a)).2 hq w hw]]
      simp [hq]
    · obtain ⟨h1, h2⟩ := (h a (mem_vars_var a)).1 hq
      rw [h1]; simp [Ty.vars, hq, h2]
  | .record ρ none, ht, h => by
    simp only [sb, Ty.vars] at ht h ⊢
    exact filter_sbRow s p q ρ ht h
  | .record ρ (some e), ht, h => by
    exfalso
    obtain ⟨a, ea⟩ := ht (.row e) (by simp [Ty.vars])
    cases ea
  | .fn a b, ht, h => by
    simp only [sb, Ty.vars, List.filter_append] at ht h ⊢
    rw [filter_sb s p q a (fun v hv => ht v (List.mem_append_left _ hv)) (fun c hc => h c (List.mem_append_left _ hc)),
      filter_sb s p q b (fun v hv => ht v (List.mem_append_right _ hv)) (fun c hc => h c (List.mem_append_right _ hc))]
  | .con as _, ht, h => by
    simp only [sb, Ty.vars] at ht h ⊢
    exact filter_sbList s p q as ht h
theorem filter_sbRow (s : FSub) (p q : BVar → Bool) : ∀ ρ : Row, (∀ v ∈ Ty.rowVars ρ, ∃ a, v = .ty a) →
    (∀ a, BVar.ty a ∈ Ty.rowVars ρ → (q (.ty a) = true → s a = .var a ∧ p (.ty a) = true) ∧
      (q (.ty a) = false → ∀ w ∈ (s a).vars, p w = false)) →
    (Ty.rowVars (sbRow s ρ)).filter p = (Ty.rowVars ρ).filter q
  | [], _, _ => rfl
  | (_, τ) :: rest, ht, h => by
    simp only [sbRow, Ty.rowVars, List.filter_append] at ht h ⊢
    rw [filter_sb s p q τ (fun v hv => ht v (List.mem_append_left _ hv)) (fun c hc => h c (List.mem_append_left _ hc)),
      filter_sbRow s p q rest (fun v hv => ht v (List.mem_append_right _ hv)) (fun c hc => h c (List.mem_append_right _ hc))]
theorem filter_sbList (s : FSub) (p q : BVar → Bool) : ∀ l : List Ty, (∀ v ∈ Ty.listVars l, ∃ a, v = .ty a) →
    (∀ a, BVar.ty a ∈ Ty.listVars l → (q (.ty a) = true → s a = .var a ∧ p (.ty a) = true) ∧
      (q (.ty a) = false → ∀ w ∈ (s a).vars, p w = false)) →
    (Ty.listVars (sbList s l)).filter p = (Ty.listVars l).filter q
  | [], _, _ => rfl
  | τ :: rest, ht, h => by
    simp only [sbList, Ty.listVars, List.filter_append] at ht h ⊢
    rw [filter_sb s p q τ (fun v hv => ht v (List.mem_append_left _ hv)) (fun c hc => h c (List.mem_append_left _ hc)),
      filter_sbList s p q rest (fun v hv => ht v (List.mem_append_right _ hv)) (fun c hc => h c (List.mem_append_right _ hc))]
end

/-! ## The commutation -/

theorem mem_VE_tyvars_sb {u : FSub} {VE0 : ValEnv} {v : BVar} (h : v ∈ (sbVE u VE0).tyvars) :
    ∃ τ ∈ veBodies VE0, v ∈ (sb u τ).vars := by
  obtain ⟨x, p, hf, hp⟩ := mem_VE_tyvars.mp h
  rw [find?_sbVE] at hf
  cases hq : FMap.find? VE0 x with
  | none => rw [hq] at hf; cases hf
  | some q =>
    rw [hq] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
    exact ⟨q.1.body, List.mem_map.mpr ⟨(x, q), find?_mem hq, rfl⟩, (mem_scheme_tyvars.mp hp).1⟩

theorem filter_nil_of {l : List BVar} {p : BVar → Bool} (h : ∀ v ∈ l, p v = false) : l.filter p = [] :=
  List.filter_eq_nil_iff.mpr fun v hv => by simp [h v hv]

theorem canonVars_noNum {bound : List BVar} {body : Ty} (h : ∀ v ∈ bound, v.isNumTyVar = false) :
    canonVars bound body = dedupL (body.vars.filter fun v => decide (v ∈ bound)) := by
  have e : ∀ occ : List BVar, bound.filter (fun v => v.isNumTyVar && !decide (v ∈ occ)) = [] :=
    fun occ => filter_nil_of (fun v hv => by simp [h v hv])
  unfold canonVars
  dsimp only
  rw [e]; simp [dedupL]

theorem filter_dedupL (p : BVar → Bool) : ∀ l : List BVar, (dedupL l).filter p = dedupL (l.filter p)
  | [] => rfl
  | x :: xs => by
    simp only [dedupL]
    cases hp : p x
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_filter, ← filter_dedupL p xs]
      congr 1; funext v
      by_cases e : v = x
      · subst e; simp [hp]
      · simp [e]
    · simp only [List.filter_cons, hp, ↓reduceIte, dedupL]
      rw [← filter_dedupL p xs, List.filter_filter, List.filter_filter]
      congr 2; funext v; simp [Bool.and_comm]

/-- Filtering the free variables of the images of a value environment, entry by entry. -/
theorem filter_tyvarsBy {f g : Scheme × IdStatus → List BVar} {p q : BVar → Bool} :
    ∀ (VE : ValEnv) (h : Scheme × IdStatus → Scheme × IdStatus) (seen : List String),
    (∀ e ∈ VE, (f (h e.2)).filter p = (g e.2).filter q) →
    (FMap.tyvarsBy f seen (VE.map fun e => (e.1, h e.2))).filter p = (FMap.tyvarsBy g seen VE).filter q
  | [], _, _, _ => rfl
  | (k, v) :: rest, h, seen, hh => by
    simp only [List.map_cons, FMap.tyvarsBy, List.filter_append]
    rw [filter_tyvarsBy rest h (k :: seen) (fun e he => hh e (.tail _ he))]
    congr 1
    have e1 := hh (k, v) (.head _)
    simp only at e1
    by_cases hk : k ∈ seen
    · simp [hk]
    · rw [show decide (k ∈ seen) = false from decide_eq_false hk, Bool.or_false, Bool.or_false]
      cases h1 : (f (h v)).isEmpty <;> cases h2 : (g v).isEmpty <;>
        (try simp only [↓reduceIte, List.filter_nil, Bool.false_eq_true])
      · exact e1
      · rw [List.isEmpty_iff] at h2; rw [h2] at e1; simpa using e1
      · rw [List.isEmpty_iff] at h1; rw [h1] at e1; simpa using e1.symm

theorem tyOnly_of_ok {τ : Ty} (h : ∀ v ∈ τ.vars, ∃ a, v = .ty a ∧ a.isBndT = false) : TyOnly τ :=
  fun v hv => by obtain ⟨a, e, _⟩ := h v hv; exact ⟨a, e⟩

theorem isBnd_ty {a : TyVar} (h : a.isBndT = false) : (BVar.ty a).isBnd = false := by
  cases a <;> simp_all [TyVar.isBndT, BVar.isBnd]

section
variable {n0 : Nat} {C : Ctx} {VE0 : ValEnv} {θ s : FSub} (H : ClosHyp n0 C VE0 θ s)
include H

theorem ClosHyp.member {τ : Ty} (hτ : τ ∈ veBodies VE0) :
    sbScheme s (closE (ctxSb θ C).tyvars (sbVE θ VE0) (mono (sb θ τ))) =
      closE (ctxSb s C).tyvars (sbVE s VE0) (mono (sb s τ)) := by
  have okτ : ∀ v ∈ τ.vars, ∃ a, v = .ty a ∧ a.isBndT = false := by
    simp only [veBodies, List.mem_map] at hτ; obtain ⟨q, hq, rfl⟩ := hτ; exact H.ok q hq
  have ok1 := H.okθ hτ
  have okS := H.sok.vars okτ
  have hsτ : sb s τ = sb s (sb θ τ) := (absorbs_sb' H.abs τ).symm
  have hL := ClosHyp.mem_L (θ := θ) hτ
  -- membership in the two bound lists
  have memL : ∀ a, TV a (sb θ τ) →
      (BVar.ty a ∈ closB (ctxSb θ C).tyvars (sbVE θ VE0) (mono (sb θ τ)) ↔
        InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) a) := by
    intro a ha
    obtain ⟨a', ea, hab⟩ := ok1 _ ha
    injection ea with ea; subst ea
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter,
      mem_dedupL, decide_eq_false_iff_not, Bool.not_eq_true', List.mem_append, not_or]
    constructor
    · rintro (⟨_, h⟩ | ⟨⟨_, h⟩, _⟩)
      · exact ⟨⟨_, hL, ha⟩, h⟩
      · exact ⟨⟨_, hL, ha⟩, h.2⟩
    · intro hg
      exact .inl ⟨mem_tyvars_iff.mpr ⟨ha, isBnd_ty hab⟩, hg.2⟩
  have memR : ∀ w ∈ (sb s τ).vars,
      (w ∈ closB (ctxSb s C).tyvars (sbVE s VE0) (mono (sb s τ)) ↔
        ∃ b, w = .ty b ∧ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b) := by
    intro w hw
    rw [← H.gen_iff hτ hw]
    obtain ⟨b, rfl, hbb⟩ := okS w hw
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter,
      mem_dedupL, decide_eq_false_iff_not, Bool.not_eq_true', List.mem_append, not_or]
    constructor
    · rintro (⟨_, h⟩ | ⟨⟨_, h⟩, _⟩)
      · exact h
      · exact h.2
    · intro h
      exact .inl ⟨mem_tyvars_iff.mpr ⟨hw, isBnd_ty hbb⟩, h⟩
  -- the A93 extras: number variables of the group's environment, generalised
  let AL := (ctxSb θ C).tyvars
  let AR := (ctxSb s C).tyvars
  let XL := ValEnv.tyvars (sbVE θ VE0)
  let XR := ValEnv.tyvars (sbVE s VE0)
  let qL : BVar → Bool := fun v => v.isNumTyVar && !decide (v ∈ (sb θ τ).tyvars) && !decide (v ∈ AL)
  let qR : BVar → Bool := fun v => v.isNumTyVar && !decide (v ∈ (sb s τ).tyvars) && !decide (v ∈ AR)
  have gR : ∀ τ' ∈ veBodies VE0, ∀ b, TV b (sb θ τ') →
      InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b → BVar.ty b ∉ AR := fun τ' hτ' b hb hg => by
    have hb' : BVar.ty b ∈ (sb s τ').vars := by
      rw [← absorbs_sb' H.abs]; exact vars_sb_of _ _ b _ hb (by rw [(H.dead b hg).1]; exact mem_vars_var b)
    exact (H.gen_iff hτ' hb').mpr ⟨b, rfl, hg⟩
  -- a generalised variable is in the image of τ exactly when it is in τ
  have occS : ∀ b, InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b →
      (BVar.ty b ∈ (sb s τ).vars ↔ TV b (sb θ τ)) := fun b hg => by
    constructor
    · intro hb
      rw [hsτ] at hb
      obtain ⟨c, hc, hbc⟩ := tyvar_sb hb
      by_cases hcg : InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) c
      · rw [(H.dead c hcg).1] at hbc
        simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hbc; subst hbc; exact hc
      · have hcA : BVar.ty c ∈ AL := Classical.byContradiction fun h => hcg ⟨⟨_, hL, hc⟩, h⟩
        exact absurd hbc ((H.dead b hg).2 c hcA)
    · intro hb; rw [hsτ]; exact vars_sb_of _ _ b _ hb (by rw [(H.dead b hg).1]; exact mem_vars_var b)
  have hX : XR.filter qR = XL.filter qL := by
    show (FMap.tyvarsBy (fun b => b.1.tyvars) [] (sbVE s VE0)).filter qR =
      (FMap.tyvarsBy (fun b => b.1.tyvars) [] (sbVE θ VE0)).filter qL
    have e1 : sbVE s VE0 = (sbVE θ VE0).map fun e => (e.1, (sbScheme s e.2.1, e.2.2)) := by
      rw [show sbVE s VE0 = sbVE s (sbVE θ VE0) by rw [sbVE_sb, comp_of_absorbs H.abs]]; rfl
    rw [e1]
    refine filter_tyvarsBy (sbVE θ VE0) (fun e => (sbScheme s e.1, e.2)) [] fun e he => ?_
    simp only [sbVE, List.mem_map] at he
    obtain ⟨q, hq, rfl⟩ := he
    have hτq : q.2.1.body ∈ veBodies VE0 := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hmq : q.2.1 = mono q.2.1.body := by
      have hb := H.isMono q hq; revert hb; obtain ⟨_, ⟨b, body⟩, _⟩ := q; intro hb; simp only at hb; subst hb; rfl
    dsimp only
    rw [hmq, sbScheme_mono, sbScheme_mono, mono_tyvars, mono_tyvars]
    simp only [Ty.tyvars, List.filter_filter]
    have okq := H.okθ hτq
    apply filter_sb s _ _ (sb θ q.2.1.body) (tyOnly_of_ok okq)
    intro a ha
    obtain ⟨a', ea, hab⟩ := okq _ ha
    injection ea with ea; subst ea
    have hnb : (BVar.ty a).isBnd = false := isBnd_ty hab
    have qLa : qL (.ty a) = true ↔ (BVar.ty a).isNumTyVar = true ∧ BVar.ty a ∉ (sb θ τ).vars ∧
        BVar.ty a ∉ AL := by
      simp [qL, mem_tyvars_iff, hnb, and_assoc]
    by_cases hg : InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) a
    · have hsa := (H.dead a hg).1
      have hnA : BVar.ty a ∉ AL := hg.2
      have hnAR := gR _ hτq a ha hg
      have hocc := occS a hg
      have qRa : qR (.ty a) = true ↔ (BVar.ty a).isNumTyVar = true ∧ BVar.ty a ∉ (sb s τ).vars ∧
          BVar.ty a ∉ AR := by
        simp [qR, mem_tyvars_iff, hnb, and_assoc]
      constructor
      · intro hq'
        refine ⟨hsa, ?_⟩
        simp only [hnb, Bool.not_false, Bool.and_true, Bool.true_and] at hq' ⊢
        obtain ⟨h1, h2, _⟩ := qLa.mp hq'
        exact qRa.mpr ⟨h1, fun h => h2 (hocc.mp h), hnAR⟩
      · intro hq' w hw
        rw [hsa] at hw; simp only [Ty.vars, List.mem_singleton] at hw; subst hw
        simp only [hnb, Bool.not_false, Bool.and_true, Bool.true_and] at hq' ⊢
        cases hr : qR (.ty a)
        · rfl
        · obtain ⟨h1, h2, _⟩ := qRa.mp hr
          rw [qLa.mpr ⟨h1, fun h => h2 (hocc.mpr h), hnA⟩] at hq'; cases hq'
    · have haA : BVar.ty a ∈ AL := Classical.byContradiction fun h =>
        hg ⟨⟨_, ClosHyp.mem_L (θ := θ) hτq, ha⟩, h⟩
      constructor
      · intro hq'
        simp only [hnb, Bool.not_false, Bool.and_true, Bool.true_and] at hq'
        exact absurd haA (qLa.mp hq').2.2
      · intro _ w hw
        cases hwb : w.isBnd
        · have hwv : w ∈ (sb s q.2.1.body).vars := by
            rw [← absorbs_sb' H.abs]; exact vars_sb_of _ _ a w ha hw
          obtain ⟨b, rfl, hbb⟩ := H.sok.vars (fun v hv => H.ok q hq v hv) w hwv
          have hbR : BVar.ty b ∈ AR := Classical.byContradiction fun hn => by
            obtain ⟨b', e, hg'⟩ := (H.gen_iff hτq hwv).mp hn
            injection e with e; subst e
            exact (H.dead b hg').2 a haA hw
          have : qR (.ty b) = false := by simp [qR, hbR]
          simp [this]
        · simp
  -- the canonical orders agree
  have occR : ∀ w, w ∈ (sb s τ).vars → (w ∈ closB AR (sbVE s VE0) (mono (sb s τ)) ↔
      ∃ b, w = .ty b ∧ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b) := memR
  have splitB : ∀ (A : List BVar) (VE : ValEnv) (τ' : Ty) (q : BVar → Bool),
      (∀ v, v ∈ (dedupL τ'.tyvars) → v ∉ A → q v = false) →
      (closB A VE (mono τ')).filter q =
        ((diffL (dedupL (ValEnv.tyvars VE)) (τ'.tyvars ++ A)).filter BVar.isNumTyVar).filter q := by
    intro A VE τ' q hq
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.filter_append]
    rw [filter_nil_of (l := diffL (dedupL τ'.tyvars) A) fun v hv => by
      simp only [diffL, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hv
      exact hq v hv.1 hv.2]
    rfl
  have extraEq : ∀ (A : List BVar) (VE : ValEnv) (τ' : Ty),
      ((diffL (dedupL (ValEnv.tyvars VE)) (τ'.tyvars ++ A)).filter BVar.isNumTyVar) =
        dedupL ((ValEnv.tyvars VE).filter fun v => v.isNumTyVar && !decide (v ∈ τ'.tyvars) && !decide (v ∈ A)) := by
    intro A VE τ'
    simp only [diffL]
    rw [List.filter_filter, filter_dedupL]
    congr 1
    apply List.filter_congr
    intro v _
    simp only [List.mem_append]
    cases v.isNumTyVar <;> by_cases h1 : v ∈ τ'.tyvars <;> by_cases h2 : v ∈ A <;> simp [h1, h2]
  have hcv : canonVars (closB AR (sbVE s VE0) (mono (sb s τ))) (sb s τ) =
      canonVars (closB AL (sbVE θ VE0) (mono (sb θ τ))) (sb θ τ) := by
    have hocc : dedupL ((sb s τ).vars.filter fun v => decide (v ∈ closB AR (sbVE s VE0) (mono (sb s τ)))) =
        dedupL ((sb θ τ).vars.filter fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))) := by
      congr 1
      have e := filter_sb s (fun v => decide (v ∈ closB AR (sbVE s VE0) (mono (sb s τ))))
        (fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))) (sb θ τ) (tyOnly_of_ok ok1)
      rw [← hsτ] at e
      apply e
      intro a ha
      constructor
      · intro hq
        have hg := (memL a ha).mp (by simpa using hq)
        have hsa := (H.dead a hg).1
        refine ⟨hsa, ?_⟩
        have hw : BVar.ty a ∈ (sb s τ).vars := by rw [hsτ]; exact vars_sb_of _ _ a _ ha (by rw [hsa]; exact mem_vars_var a)
        simpa using (memR _ hw).mpr ⟨a, rfl, hg⟩
      · intro hq w hw
        have hng : ¬ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) a := fun hg => by
          have := (memL a ha).mpr hg
          exact absurd this (by simpa using hq)
        have haA : BVar.ty a ∈ (ctxSb θ C).tyvars := Classical.byContradiction fun h => hng ⟨⟨_, hL, ha⟩, h⟩
        have hw' : w ∈ (sb s τ).vars := by rw [hsτ]; exact vars_sb_of _ _ a _ ha hw
        cases hm : decide (w ∈ closB (ctxSb s C).tyvars (sbVE s VE0) (mono (sb s τ)))
        · rfl
        · obtain ⟨b, rfl, hg⟩ := (memR w hw').mp (by simpa using hm)
          exact absurd hw ((H.dead b hg).2 a haA)
    unfold canonVars
    dsimp only
    rw [hocc]
    congr 2
    -- the extras
    have hR := splitB AR (sbVE s VE0) (sb s τ)
      (fun v => v.isNumTyVar && !decide (v ∈ dedupL ((sb θ τ).vars.filter
        fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))))) (fun v hv hvA => by
          rw [mem_dedupL, mem_tyvars_iff] at hv
          obtain ⟨b, rfl, -⟩ := okS _ hv.1
          have hg : InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) b := by
            obtain ⟨b', e, hg⟩ := (H.gen_iff hτ hv.1).mp hvA; injection e with e; subst e; exact hg
          have hb := (occS b hg).mp hv.1
          have hm : BVar.ty b ∈ dedupL ((sb θ τ).vars.filter
              fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))) :=
            mem_dedupL.mpr (List.mem_filter.mpr ⟨hb, decide_eq_true ((memL b hb).mpr hg)⟩)
          simp [hm])
    have hL' := splitB AL (sbVE θ VE0) (sb θ τ)
      (fun v => v.isNumTyVar && !decide (v ∈ dedupL ((sb θ τ).vars.filter
        fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))))) (fun v hv hvA => by
          rw [mem_dedupL, mem_tyvars_iff] at hv
          obtain ⟨b, rfl, -⟩ := ok1 _ hv.1
          have hm : BVar.ty b ∈ dedupL ((sb θ τ).vars.filter
              fun v => decide (v ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)))) :=
            mem_dedupL.mpr (List.mem_filter.mpr ⟨hv.1, decide_eq_true ((memL b hv.1).mpr ⟨⟨_, hL, hv.1⟩, hvA⟩)⟩)
          simp [hm])
    rw [hR, hL', extraEq, extraEq]
    show (dedupL (XR.filter qR)).filter _ = (dedupL (XL.filter qL)).filter _
    rw [hX]
  -- membership in the bound list of W's closure
  have inGL : ∀ c, BVar.ty c ∈ closB AL (sbVE θ VE0) (mono (sb θ τ)) →
      InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) c := by
    intro c hc
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter,
      mem_dedupL, decide_eq_false_iff_not, Bool.not_eq_true', List.mem_append, not_or] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, _⟩
    · exact ⟨⟨_, hL, (mem_tyvars_iff.mp h1).1⟩, h2⟩
    · obtain ⟨τ', hτ', hv'⟩ := mem_VE_tyvars_sb h1
      exact ⟨⟨_, ClosHyp.mem_L (θ := θ) hτ', hv'⟩, h2.2⟩
  -- the closures
  have btL := closE_bound_ty (A := (ctxSb θ C).tyvars) (VE := sbVE θ VE0) (tyOnly_of_ok ok1)
  have btR := closE_bound_ty (A := (ctxSb s C).tyvars) (VE := sbVE s VE0) (tyOnly_of_ok okS)
  obtain ⟨as1, hcv1, hc1⟩ := canon_ty (body := sb θ τ) btL
  obtain ⟨as2, hcv2, hc2⟩ := canon_ty (body := sb s τ) btR
  have has : as2 = as1 := by
    rw [hcv, hcv1] at hcv2
    exact (List.map_inj_right (fun x y h => by injection h)).mp hcv2.symm
  subst has
  -- membership in the renamed list
  have memAs : ∀ a, TV a (sb θ τ) → (a ∈ as2 ↔ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) a) := by
    intro a ha
    rw [← memL a ha]
    have : a ∈ as2 ↔ BVar.ty a ∈ as2.map BVar.ty := by simp
    rw [this, ← hcv1, mem_canonVars_iff ha]
  unfold closE
  rw [mono_body, mono_body, hc1, hc2]
  simp only [sbScheme, Scheme.mk.injEq, true_and]
  rw [hsτ, sb_sb (lk (rnTy 0 as2)) s (sb θ τ), sb_sb s (lk (rnTy 0 as2)) (sb θ τ)]
  apply sb_congr
  intro a ha
  simp only [comp, lk_rnTy]
  by_cases hm : a ∈ as2
  · rw [if_pos hm]
    have hg := (memAs a ha).mp hm
    rw [(H.dead a hg).1]
    simp only [sb, lk_rnTy, if_pos hm]
    exact H.sok.bnd _ _
  · rw [if_neg hm]
    simp only [sb]
    symm
    refine sb_eq_self_iff.mpr fun c hc => ?_
    rw [lk_rnTy, if_neg]
    intro hc'
    have hng : ¬ InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) a := fun hg => hm ((memAs a ha).mpr hg)
    have haA : BVar.ty a ∈ (ctxSb θ C).tyvars := Classical.byContradiction fun h => hng ⟨⟨_, hL, ha⟩, h⟩
    have hcg : InG ((ctxSb θ C).tyvars, veBodies (sbVE θ VE0)) c := by
      have := List.mem_map_of_mem (f := BVar.ty) hc'
      rw [← hcv1] at this
      exact inGL c (mem_canonVars this)
    exact (H.dead c hcg).2 a haA hc

/-- The closure at a `let` commutes with a later substitution respecting its constraint. -/
theorem closGroup_sb :
    sbVE s (closGroup (ctxSb θ C).tyvars (sbVE θ VE0)) = closGroup (ctxSb s C).tyvars (sbVE s VE0) := by
  rw [closGroup_eq, closGroup_eq]
  simp only [sbVE, FMap.mapV, List.map_map]
  apply List.map_congr_left
  intro q hq
  obtain ⟨x, ⟨bd, τ⟩, st⟩ := q
  have hb : bd = [] := H.isMono _ hq
  subst hb
  have hτ : τ ∈ veBodies VE0 := List.mem_map.mpr ⟨_, hq, rfl⟩
  simp only [Function.comp, Prod.mk.injEq, true_and, and_true]
  exact H.member hτ

end

end StandardElm.Stat.Complete
