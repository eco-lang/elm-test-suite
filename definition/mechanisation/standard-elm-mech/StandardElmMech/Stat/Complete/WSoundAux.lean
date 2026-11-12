/-
  A Standard Definition of Elm? Mechanisation: lemmas for the expression cases of L10 (plan step
  11, milestone (b)): contexts under substitution, the free variables of `θ C` at a closure, the
  constraint a closure records (`kseg_clos`), group entries, constructor lookups that a pattern
  binding's own variables do not shadow (`checkAtPat_lkC`).
-/
import StandardElmMech.Stat.Complete.WSoundPat

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Contexts under substitution -/

theorem ctxSb_plusVE (s : FSub) (C : Ctx) (VE : ValEnv) :
    ctxSb s (C.plusVE VE) = (ctxSb s C).plusVE (sbVE s VE) := by
  simp [ctxSb, Ctx.plusVE, sbVE]

theorem ctxSb_U (s : FSub) (C : Ctx) : (ctxSb s C).U = C.U := rfl

theorem ctxSb_lookupTy (s : FSub) (C : Ctx) (lc : LongId) : (ctxSb s C).lookupTy lc = C.lookupTy lc := rfl

theorem plusVE_lookupTy (C : Ctx) (VE : ValEnv) (lc : LongId) : (C.plusVE VE).lookupTy lc = C.lookupTy lc := rfl

/-- The context's status of a name is kept by a substitution. -/
theorem lookupVal_ctxSb_c {s : FSub} {C : Ctx} {lv : LongId} {σ : Scheme}
    (h : (ctxSb s C).lookupVal lv = some (σ, .c)) : ∃ σ0, C.lookupVal lv = some (σ0, .c) := by
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at h ⊢
    change FMap.find? (sbVE s C.E.VE) lv.id = _ at h
    rw [find?_sbVE] at h
    cases hf : FMap.find? C.E.VE lv.id with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p.1, by rw [← h.2]⟩
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at h ⊢
    exact ⟨σ, h⟩

/-! ## Constructor lookups in a pattern binding's context -/

mutual
theorem checkAtPat_lkC {C1 C2 : Ctx} (h : LkC C1 C2) : ∀ p : AAtPat, checkAtPat C1 p = true → checkAtPat C2 p = true
  | .wild _, hc | .scon _ _, hc | .var _ _, hc | .unit, hc | .nil _, hc => hc
  | .con lc inst τ, hc => by
    simp only [checkAtPat] at hc ⊢
    split at hc
    · rename_i σ hl; rw [h _ _ hl]; exact hc
    · cases hc
  | .tuple p1 p2 p3, hc => by
    simp only [checkAtPat, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨checkPat_lkC h p1 hc.1.1, checkPat_lkC h p2 hc.1.2⟩, checkPatOpt_lkC h p3 hc.2⟩
  | .record row τ, hc => by
    simp only [checkAtPat, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨checkPatRowOpt_lkC h row hc.1.1, hc.1.2⟩, hc.2⟩
  | .paren p, hc => by simp only [checkAtPat] at hc ⊢; exact checkPat_lkC h p hc
theorem checkPatRow_lkC {C1 C2 : Ctx} (h : LkC C1 C2) : ∀ r : APatRow, checkPatRow C1 r = true → checkPatRow C2 r = true
  | .field _ _ rest, hc => by simp only [checkPatRow] at hc ⊢; exact checkPatRowOpt_lkC h rest hc
theorem checkPatRowOpt_lkC {C1 C2 : Ctx} (h : LkC C1 C2) :
    ∀ r : Option APatRow, checkPatRowOpt C1 r = true → checkPatRowOpt C2 r = true
  | none, _ => rfl
  | some r, hc => by simp only [checkPatRowOpt] at hc ⊢; exact checkPatRow_lkC h r hc
theorem checkPat_lkC {C1 C2 : Ctx} (h : LkC C1 C2) : ∀ p : APat, checkPat C1 p = true → checkPat C2 p = true
  | .atpat a, hc => by simp only [checkPat] at hc ⊢; exact checkAtPat_lkC h a hc
  | .con lc inst args τ, hc => by
    simp only [checkPat, Bool.and_eq_true] at hc ⊢
    refine ⟨?_, checkAtPatList_lkC h args hc.2⟩
    have hc1 := hc.1
    split at hc1
    · rename_i σ hl; rw [h _ _ hl]; exact hc1
    · cases hc1
  | .cons p1 p2, hc => by
    simp only [checkPat, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨checkPat_lkC h p1 hc.1.1, checkPat_lkC h p2 hc.1.2⟩, hc.2⟩
  | .as p _, hc => by simp only [checkPat] at hc ⊢; exact checkPat_lkC h p hc
theorem checkPatOpt_lkC {C1 C2 : Ctx} (h : LkC C1 C2) : ∀ p : Option APat, checkPatOpt C1 p = true → checkPatOpt C2 p = true
  | none, _ => rfl
  | some p, hc => by simp only [checkPatOpt] at hc ⊢; exact checkPat_lkC h p hc
theorem checkAtPatList_lkC {C1 C2 : Ctx} (h : LkC C1 C2) :
    ∀ l : List AAtPat, checkAtPatList C1 l = true → checkAtPatList C2 l = true
  | [], _ => rfl
  | a :: as, hc => by
    simp only [checkAtPatList, Bool.and_eq_true] at hc ⊢
    exact ⟨checkAtPat_lkC h a hc.1, checkAtPatList_lkC h as hc.2⟩
end

/-- A pattern binding none of whose variables names a constructor of `C`: the checker's context
    with the variables finds the constructors the checker's context without them finds. -/
theorem lkC_noShadow {s : FSub} {C : Ctx} {VE : ValEnv} (h : (VE.all fun q => !conBound C q.1) = true) :
    LkC (ctxSb s C) ((ctxSb s C).plusVE (sbVE s VE)) := by
  intro lv σ hl
  rw [lookupVal_plusVE]
  cases hq : lv.qual with
  | none =>
    simp only
    cases hf : FMap.find? (sbVE s VE) lv.id with
    | none => simp only [Option.none_or]; simpa [Ctx.lookupVal, Env.lookupVal, hq] using hl
    | some p =>
      exfalso
      rw [find?_sbVE] at hf
      cases hf' : FMap.find? VE lv.id with
      | none => rw [hf'] at hf; cases hf
      | some p0 =>
        have hm := find?_mem hf'
        have := List.all_eq_true.mp h _ hm
        obtain ⟨σ0, hl0⟩ := lookupVal_ctxSb_c hl
        have hl1 : C.lookupVal ⟨none, lv.id⟩ = some (σ0, .c) := by
          rw [← hl0]; cases lv; simp_all
        simp [conBound, hl1] at this
  | some m => simpa using hl

/-! ## The free variables of `θ C` at a closure -/

section
variable {n0 : Nat} {C : Ctx} {st : WSt} (hp : SPre n0 C st)
include hp

theorem SPre.ctxB : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.bound, v.isBnd = true :=
  fun x p hf => (hp.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])).1

theorem SPre.ctxF : ∀ x p, FMap.find? C.E.VE x = some p → ∀ v ∈ p.1.body.vars, v ∉ p.1.bound →
    ∃ a, v = .ty a ∧ a.isBndT = false := fun x p hf v hv hb => by
  obtain ⟨a, e, h1, -⟩ := (hp.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])).2 v hv hb
  exact ⟨a, e, h1⟩

/-- A free variable of `θ C` is a variable of the image of a free variable of `C`. -/
theorem SPre.A_src {θ : FSub} (hθ : SOk n0 θ) {c : TyVar} (h : BVar.ty c ∈ (ctxSb θ C).tyvars) :
    ∃ c', BVar.ty c' ∈ C.tyvars ∧ TV c (θ c') := by
  rcases ctxSb_tyvars_mem (fun i c => hθ.bnd i c) hp.ctxB h with hr | ⟨x, p, e, hf, he, hnb, hce⟩ | ⟨_, _, _, _, r, hr⟩
  · refine ⟨c, mem_ctx_tyvars.mpr (.inl hr), ?_⟩
    rw [hθ.1 _ (hp.rest c hr)]; exact mem_vars_var c
  · obtain ⟨a, ea, hab⟩ := hp.ctxF x p hf _ he hnb
    cases ea
    exact ⟨e, mem_ctx_tyvars.mpr (.inr ⟨x, p, hf, mem_scheme_tyvars.mpr ⟨he, isBnd_ty hab, hnb⟩⟩), hce⟩
  · cases hr

theorem SPre.A_fixed {θ : FSub} (hθ : SOk n0 θ) (hi : Idem θ) {c : TyVar} (h : BVar.ty c ∈ (ctxSb θ C).tyvars) :
    θ c = .var c := by
  obtain ⟨c', _, hc⟩ := hp.A_src hθ h
  exact hi c' c hc

/-- The image of a free variable of `C` is free in `θ C`. -/
theorem SPre.inA {θ : FSub} (hθ : SOk n0 θ) {c b : TyVar} (hc : BVar.ty c ∈ C.tyvars) (hb : TV b (θ c)) :
    BVar.ty b ∈ (ctxSb θ C).tyvars := by
  rcases mem_ctx_tyvars.mp hc with hr | ⟨x, p, hf, hcp⟩
  · rw [hθ.1 _ (hp.rest c hr)] at hb
    simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
    exact mem_ctx_tyvars.mpr (.inl hr)
  · obtain ⟨hc1, hc2, -⟩ := mem_scheme_tyvars.mp hcp
    have hbb : b.isBndT = false := by
      by_cases e : θ c = .var c
      · rw [e] at hb; simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
        cases b <;> simp_all [BVar.isBnd, TyVar.isBndT]
      · obtain ⟨b', e', h'⟩ := hθ.2 c (by cases c <;> simp_all [BVar.isBnd, TyVar.isBndT]) _ hb
        cases e'; exact h'
    exact ctxSb_tyvars_of hp.ctxB (isBnd_ty hbb) hf hc1 hb

end

/-- The free variables of a member's closure: free in the context. -/
theorem closE_tyvars {A : List BVar} {VE : ValEnv} {τ : Ty} (hτ : TyOnly τ) {v : BVar}
    (h : v ∈ (closE A VE (mono τ)).tyvars) : v ∈ τ.vars ∧ v ∈ A := by
  obtain ⟨as, hcv, hc⟩ := canon_ty (body := τ) (closE_bound_ty (A := A) (VE := VE) hτ)
  unfold closE at h
  rw [mono_body, hc] at h
  obtain ⟨h1, h2, -⟩ := mem_scheme_tyvars.mp h
  simp only at h1
  rcases vars_sb _ τ v h1 with ⟨r, rfl, hr⟩ | ⟨a, ha, hva⟩
  · obtain ⟨a, e⟩ := hτ _ hr; cases e
  · rw [lk_rnTy] at hva
    split at hva
    · simp only [Ty.vars, List.mem_singleton] at hva; subst hva; simp [BVar.isBnd] at h2
    · rename_i hm
      simp only [Ty.vars, List.mem_singleton] at hva; subst hva
      refine ⟨ha, Classical.byContradiction fun hA => hm ?_⟩
      have : BVar.ty a ∈ canonVars (closB A VE (mono τ)) τ := by
        rw [mem_canonVars_iff ha]
        simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter,
          mem_dedupL, decide_eq_false_iff_not, Bool.not_eq_true']
        exact .inl ⟨mem_tyvars_iff.mpr ⟨ha, h2⟩, hA⟩
      rw [hcv] at this; simpa using this

/-! ## The constraint a closure records -/

theorem PostK.addK {n0 : Nat} {C : Ctx} {st st1 : WSt} {Chk : FSub → Prop} {K : List ConW} {k : ConW}
    (h : PostK n0 C st st1 [] Chk K) (hk : KSeg [k] st st1) :
    PostK n0 C st st1 [] (fun s => Chk s ∧ DeadC k s) (k :: K) :=
  ⟨h.seg, (fun _ h => nomatch h), (fun _ h => nomatch h),
    ⟨fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.dead k (.head _)) (h.ks.dead k'),
     fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.zone k (.head _)) (h.ks.zone k'),
     fun k' hk' => (List.mem_cons.mp hk').elim (fun e => e ▸ hk.old k (.head _)) (h.ks.old k')⟩,
    (fun _ h => nomatch h),
    fun s h1 h2 h3 => ⟨h.chk s h1 h2 fun k' hk' => h3 k' (.tail _ hk'), h3 k (.head _)⟩⟩

theorem SInv.sok {n0 : Nat} {st : WSt} (hi : SInv n0 st) : SOk n0 (lk st.θ) := by
  refine ⟨hi.good.fixesR, fun a ha v hv => ?_, hi.good.respC⟩
  rcases hi.ok a with e | ⟨-, hok⟩
  · rw [e] at hv; simp only [Ty.vars, List.mem_singleton] at hv; subst hv; exact ⟨a, rfl, ha⟩
  · obtain ⟨b, e, h1, -⟩ := hok v hv; exact ⟨b, e, h1⟩

/-- The constraint recorded at a `let`: it holds now, its generalised variables are new, and the
    images of the old variables avoid them. -/
theorem kseg_clos {n0 : Nat} {C : Ctx} {st st1 : WSt} {VE0 : ValEnv} (hp : SPre n0 C st)
    (hs : Seg n0 (Reach (lk st.θ) C st.n) st st1)
    (hok : ∀ τ ∈ veBodies VE0, OkT st1.n τ)
    (hr : ∀ τ ∈ veBodies VE0, ∀ b, TV b (sb (lk st1.θ) τ) → Reach (lk st.θ) C st.n b) :
    KSeg [((ctxSb (lk st1.θ) C).tyvars, veBodies (sbVE (lk st1.θ) VE0))] st st1 := by
  have hi1 := hs.inv
  have hi := hp.inv
  have hθ1 := hi1.sok
  -- a generalised variable is in an image under θ1, so θ1 fixes it
  have hfix : ∀ b, InG ((ctxSb (lk st1.θ) C).tyvars, veBodies (sbVE (lk st1.θ) VE0)) b → lk st1.θ b = .var b := by
    rintro b ⟨⟨τ1, hτ1, hb⟩, -⟩
    simp only [veBodies, sbVE, List.map_map, List.mem_map, Function.comp] at hτ1
    obtain ⟨q, -, rfl⟩ := hτ1
    obtain ⟨a, -, hba⟩ := tyvar_sb hb
    exact hi1.good.idem a b hba
  have hsrc : ∀ b, InG ((ctxSb (lk st1.θ) C).tyvars, veBodies (sbVE (lk st1.θ) VE0)) b →
      ∃ τ ∈ veBodies VE0, TV b (sb (lk st1.θ) τ) := by
    rintro b ⟨⟨τ1, hτ1, hb⟩, -⟩
    simp only [veBodies, sbVE, List.map_map, List.mem_map, Function.comp] at hτ1
    obtain ⟨q, hq, rfl⟩ := hτ1
    exact ⟨q.2.1.body, List.mem_map.mpr ⟨q, hq, rfl⟩, hb⟩
  -- the image under θ1 of a variable of the image under θ of a free variable is free in θ1 C
  have hA : ∀ c b, BVar.ty c ∈ C.tyvars → TV b (lk st.θ c) → lk st1.θ b = .var b →
      BVar.ty b ∈ (ctxSb (lk st1.θ) C).tyvars := by
    intro c b hc hb hfb
    refine hp.inA hθ1 hc ?_
    rw [← hs.abs c]
    exact vars_sb_of _ _ b _ hb (by rw [hfb]; exact mem_vars_var b)
  have hnew : ∀ b, InG ((ctxSb (lk st1.θ) C).tyvars, veBodies (sbVE (lk st1.θ) VE0)) b → b.isNew st.n = true := by
    intro b hg
    obtain ⟨τ, hτ, hb⟩ := hsrc b hg
    rcases hr τ hτ b hb with h | ⟨c, hc, hcb⟩
    · exact h
    · exact absurd (hA c b hc hcb (hfix b hg)) hg.2
  refine ⟨fun k hk b hg => ?_, fun k hk b hg => ?_, fun k hk b hg a ha hba => ?_⟩
  · simp only [List.mem_singleton] at hk; subst hk
    refine ⟨hfix b hg, fun a ha hba => ?_⟩
    rw [hp.A_fixed hθ1 hi1.good.idem ha] at hba
    simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hba; subst hba
    exact hg.2 ha
  · simp only [List.mem_singleton] at hk; subst hk
    refine ⟨hnew b hg, ?_⟩
    obtain ⟨τ, hτ, hb⟩ := hsrc b hg
    obtain ⟨b', e, -, h⟩ := hi1.ok.okT (hok τ hτ) _ hb
    cases e; exact h
  · simp only [List.mem_singleton] at hk; subst hk
    rcases moves_ty hs.mv hs.abs hi.good.idem (.var a) b hba with ⟨h1, -⟩ | ⟨e, he, -, -, hre, -, hbe⟩
    · -- b in the old image: old
      change TV b (lk st.θ a) at h1
      have : b.isNew st.n = false := by
        rcases hi.ok a with e | ⟨-, hok'⟩
        · rw [e] at h1; simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at h1; subst h1; exact ha
        · obtain ⟨b', e', -, h⟩ := hok' _ h1; cases e'; exact h
      rw [hnew b hg] at this; cases this
    · change TV e (lk st.θ a) at he
      have heo : e.isNew st.n = false := by
        rcases hi.ok a with e' | ⟨-, hok'⟩
        · rw [e'] at he; simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at he; subst he; exact ha
        · obtain ⟨b', e', -, h⟩ := hok' _ he; cases e'; exact h
      rcases hre with h | ⟨c, hc, hce⟩
      · rw [heo] at h; cases h
      · apply hg.2
        refine hp.inA hθ1 hc ?_
        rw [← hs.abs c]
        exact vars_sb_of _ _ e _ hce hbe

/-! ## Group entries -/

theorem checkAnn_closed {C' : Ctx} {ty : BTy} {τ : Ty} (hb : bTyNames ty = []) (hU : Unambiguous C'.U)
    (hel : elabTy (C'.plusU []) ty = some τ) : checkAnn C' (some (ty, [])) τ = true := by
  simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, Bool.and_true, hel, and_true]
  unfold newForB
  simp [hb, namesU, hU]

/-- A group entry (`groupEntries`' first step). -/
def entryW (C : Ctx) : Option BTy → WM (Option (BTy × List BVar) × Ty)
  | none => do let α ← freshV; pure ((none : Option (BTy × List BVar)), α)
  | some ty =>
    if (Stat.bTyNames ty).isEmpty && decide (Unambiguous C.U) then
      match elabTy (C.plusU []) ty with
      | some τ => if τ.vars.isEmpty then pure (some (ty, []), τ) else wUnsupported
      | none => wFail
    else wUnsupported

theorem groupEntries_var (C : Ctx) (x : String) (ann : Option BTy) (e : BExp) (rest : Option BValBind) (st : WSt) :
    groupEntries C (.var x ann e rest) st = (do
      let en ← entryW C ann
      let es ← (match rest with | none => pure [] | some vb => groupEntries C vb)
      pure (en :: es)) st := by
  cases ann with
  | none => cases rest <;> rfl
  | some ty =>
    cases rest <;>
    · simp only [groupEntries, entryW]
      by_cases hc : ((bTyNames ty).isEmpty && decide (Unambiguous C.U)) = true
      · rw [if_pos hc, if_pos hc]
        cases hel : elabTy (C.plusU []) ty with
        | none => rfl
        | some τ =>
          by_cases hv : τ.vars.isEmpty = true
          · simp only [hv, ↓reduceIte]
          · simp only [hv, ↓reduceIte, Bool.false_eq_true]
      · rw [if_neg hc, if_neg hc]

theorem groupEntries_sound {n0 : Nat} {C : Ctx} :
    ∀ (vb : BValBind) (st : WSt) (es : List (Option (BTy × List BVar) × Ty)) (st' : WSt), SPre n0 C st →
      groupEntries C vb st = .ok es st' →
      (∀ e ∈ es, annU e.1 = [] ∧ ∀ (C' : Ctx) (s : FSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' e.1 (sb s e.2) = true) ∧
      PostK n0 C st st' (es.map (·.2)) (fun _ => True) []
  | .pat _ _, st, es, st', hp, h => by unfold groupEntries at h; cases h
  | .var x ann e rest, st, es, st', hp, h => by
    rw [groupEntries_var] at h
    obtain ⟨en, st1, h1, h⟩ := wbind_ok h
    obtain ⟨es', st2, h2, h⟩ := wbind_ok h
    -- the first entry
    have P1 : (annU en.1 = [] ∧ ∀ (C' : Ctx) (s : FSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' en.1 (sb s en.2) = true) ∧ PostK n0 C st st1 [en.2] (fun _ => True) [] := by
      cases ann with
      | none =>
        simp only [entryW] at h1
        obtain ⟨α, st0, h0, h1'⟩ := wbind_ok h1
        obtain ⟨rfl, rfl⟩ := freshV_ok h0
        obtain ⟨rfl, rfl⟩ := pure_ok' h1'
        exact ⟨⟨rfl, fun _ _ _ _ => rfl⟩, (PostK.start hp).fresh⟩
      | some ty =>
        simp only [entryW] at h1
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
              obtain ⟨rfl, rfl⟩ := pure_ok' h1
              refine ⟨⟨rfl, fun C' s hU hT => ?_⟩, PostK.closed hp hv' fun _ _ => trivial⟩
              have hb : bTyNames ty = [] := by simpa using hc.1
              rw [sb_closed hv']
              refine checkAnn_closed hb (by rw [hU]; exact hc.2) ?_
              rw [elabTy_congrW (C1 := C'.plusU []) (C2 := C.plusU []) (by simp [Ctx.plusU, hU])
                (fun lc => by simp only [plusU_nil]; exact hT lc)]
              exact hel
            · simp only [hv, ↓reduceIte, Bool.false_eq_true] at h1; cases h1
        · rw [if_neg hc] at h1; cases h1
    have hp1 := hp.later P1.2.seg
    -- the rest
    have P2 : (∀ e ∈ es', annU e.1 = [] ∧ ∀ (C' : Ctx) (s : FSub), C'.U = C.U → (∀ lc, C'.lookupTy lc = C.lookupTy lc) →
        checkAnn C' e.1 (sb s e.2) = true) ∧ PostK n0 C st1 st2 (es'.map (·.2)) (fun _ => True) [] := by
      cases rest with
      | none =>
        simp only at h2
        obtain ⟨rfl, rfl⟩ := pure_ok' h2
        exact ⟨(fun _ h => nomatch h), PostK.start hp1⟩
      | some vb => exact groupEntries_sound vb st1 es' st2 hp1 h2
    obtain ⟨rfl, rfl⟩ := pure_ok' h
    refine ⟨fun e' he' => (List.mem_cons.mp he').elim (fun e => e ▸ P1.1) (P2.1 e'), ?_⟩
    exact (P1.2.seq P2.2 (reach_same P1.2.seg hp.inv) (avoid_same hp P1.2.ks)).weaken
      (covSub fun τ hτ => by simpa using hτ) fun _ _ _ => trivial

/-! ## Composition helpers -/

theorem PostK.seqSame {n0 : Nat} {C : Ctx} {st st1 st2 : WSt} {tys1 tys2 : List Ty} {Chk1 Chk2 : FSub → Prop}
    {K1 K2 : List ConW} (hp : SPre n0 C st) (h1 : PostK n0 C st st1 tys1 Chk1 K1) (h2 : PostK n0 C st1 st2 tys2 Chk2 K2) :
    PostK n0 C st st2 (tys1 ++ tys2) (fun s => Chk1 s ∧ Chk2 s) (K2 ++ K1) :=
  h1.seq h2 (reach_same h1.seg hp.inv) (avoid_same hp h1.ks)

theorem PostK.withAbs {n0 : Nat} {C : Ctx} {st st1 : WSt} {tys : List Ty} {Chk : FSub → Prop} {K : List ConW}
    (h : PostK n0 C st st1 tys Chk K) : PostK n0 C st st1 tys (fun s => Chk s ∧ Absorbs s (lk st1.θ)) K :=
  { h with chk := fun s h1 h2 h3 => ⟨h.chk s h1 h2 h3, h2⟩ }

/-- A context extended by entries whose types are covered by the types a call returned. -/
theorem PostK.plusVE_pre {n0 : Nat} {C : Ctx} {st st1 : WSt} {tys : List Ty} {Chk : FSub → Prop} {K : List ConW}
    {VE : ValEnv} (hp : SPre n0 C st) (h : PostK n0 C st st1 tys Chk K)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ ∀ v ∈ q.2.1.body.vars, ∃ τ ∈ tys, v ∈ τ.vars) :
    SPre n0 (C.plusVE VE) st1 ∧ (∀ b, Reach (lk st1.θ) (C.plusVE VE) st1.n b → Reach (lk st.θ) C st.n b) ∧
      AvoidK K (Reach (lk st1.θ) (C.plusVE VE) st1.n) := by
  have hq : ∀ q ∈ VE, PostK n0 C st st1 [q.2.1.body] Chk K := fun q hq =>
    h.weaken (fun τ hτ v hv => by simp only [List.mem_singleton] at hτ; subst hτ; exact (hVE q hq).2 v hv)
      fun _ _ c => c
  refine ⟨hp.plusVE h.seg.le h.seg.inv h.seg.any fun q hq' => ?_, reach_plusVE h.seg hp.inv fun q hq' =>
    (hq q hq').reach _ (.head _), avoid_plusVE hp h.ks fun q hq' => (hq q hq').tyav _ (.head _)⟩
  exact monoEnt (hVE q hq').1 ((hq q hq').okT _ (.head _)).1 ((hq q hq').okT _ (.head _)).2

theorem cov_tuple {τ1 τ2 : Ty} {τ3 : Option Ty} : Cov [tupleTy τ1 τ2 τ3] ([τ1] ++ [τ2] ++ τ3.toList) := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  rcases vars_tupleTy hv with h | h | ⟨τ, rfl, h⟩
  · exact ⟨τ1, by simp, h⟩
  · exact ⟨τ2, by simp, h⟩
  · exact ⟨τ, by simp, h⟩

theorem cov_fn {τ1 τ2 : Ty} {l : List Ty} (h1 : ∀ v ∈ τ1.vars, ∃ τ ∈ l, v ∈ τ.vars)
    (h2 : ∀ v ∈ τ2.vars, ∃ τ ∈ l, v ∈ τ.vars) : Cov [Ty.fn τ1 τ2] l := by
  intro x hx v hv
  simp only [List.mem_singleton] at hx; subst hx
  simp only [Ty.vars, List.mem_append] at hv
  rcases hv with hv | hv
  · exact h1 v hv
  · exact h2 v hv

theorem mem_self_vars {τ : Ty} {l : List Ty} (h : τ ∈ l) : ∀ v ∈ τ.vars, ∃ τ' ∈ l, v ∈ τ'.vars :=
  fun v hv => ⟨τ, h, hv⟩

/-- An entry of the closure W takes at a `let`. -/
theorem closGroup_mem {A : List BVar} {θ : FSub} {VE0 : ValEnv} (hm : ∀ q ∈ VE0, q.2.1.bound = [])
    {q : String × (Scheme × IdStatus)} (hq : q ∈ closGroup A (sbVE θ VE0)) :
    ∃ q0 ∈ VE0, q = (q0.1, closE A (sbVE θ VE0) (mono (sb θ q0.2.1.body)), q0.2.2) := by
  rw [closGroup_eq] at hq
  simp only [FMap.mapV, sbVE, List.map_map, List.mem_map, Function.comp] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  refine ⟨q0, hq0, ?_⟩
  obtain ⟨x, ⟨bd, τ⟩, st⟩ := q0
  have : bd = [] := hm _ hq0
  subst this
  rfl

end StandardElm.Stat.Complete
