/-
  A Standard Definition of Elm? Mechanisation: W's state invariant, its instantiation as the most
  general instance (L2), and the root context, for the main induction L11 (plan step 11,
  milestone (b), section 8).

  `SInv n0 st`: the counter is at least the root's `n0`; the accumulated substitution is good
  (MguC.lean: idempotent, binding only flexible variables, to admissible types of their classes) and binds only variables
  below the counter, each to a type W builds (`OkT`).
-/
import StandardElmMech.Stat.Complete.WRel

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-- The substitution binds only old variables, to types W builds. -/
def ThetaOk (n : Nat) (θ : Bnd) : Prop :=
  ∀ a, lk θ a = .var a ∨ (a.isNew n = false ∧ OkT n (lk θ a))

/-- The bindings are of old variables, to types W builds. -/
def BndOk (n : Nat) (θ : Bnd) : Prop := ∀ p ∈ θ, p.1.isNew n = false ∧ OkT n p.2

structure SInv (n0 : Nat) (st : WSt) : Prop where
  le : n0 ≤ st.n
  good : GoodC (rigidFrom n0) st.n st.θ []
  okL : BndOk st.n st.θ

theorem BndOk.mono {n m : Nat} (h : n ≤ m) {θ : Bnd} (hθ : BndOk n θ) : BndOk m θ := fun p hp =>
  ⟨isNew_mono h (hθ p hp).1, (hθ p hp).2.mono h⟩

theorem BndOk.thetaOk {n : Nat} {θ : Bnd} (h : BndOk n θ) : ThetaOk n θ := fun a => by
  unfold lk
  cases hf : FMap.find? θ a with
  | none => exact .inl rfl
  | some τ => exact .inr (h _ (find?_mem hf))

theorem SInv.ok {n0 : Nat} {st : WSt} (h : SInv n0 st) : ThetaOk st.n st.θ := h.okL.thetaOk

theorem ThetaOk.mono {n m : Nat} (h : n ≤ m) {θ : Bnd} (hθ : ThetaOk n θ) : ThetaOk m θ := fun a => by
  rcases hθ a with h1 | ⟨h1, h2⟩
  · exact .inl h1
  · exact .inr ⟨isNew_mono h h1, h2.mono h⟩

theorem ThetaOk.okT {n : Nat} {θ : Bnd} (hθ : ThetaOk n θ) {τ : Ty} (hτ : OkT n τ) : OkT n (sb (lk θ) τ) :=
  OkT_sb hτ fun a ha => by
    rcases hθ a with h1 | ⟨_, h2⟩
    · rw [h1]; obtain ⟨b, e, h3, h4⟩ := hτ _ ha; cases e; exact OkT_var h3 h4
    · exact h2

theorem SInv.fresh {n0 : Nat} {st : WSt} (h : SInv n0 st) : SInv n0 { st with n := st.n + 1 } :=
  ⟨Nat.le_succ_of_le h.le, h.good.mono (Nat.le_succ _), h.okL.mono (Nat.le_succ _)⟩

/-- A substitution that agrees with `s` on the old variables fixes the rigid ones and absorbs `θ`
    when `s` does. -/
theorem agree_ok {n0 n : Nat} (h0 : n0 ≤ n) {θ : Bnd} (hθ : ThetaOk n θ) {s T : FSub}
    (hs : FixesR (rigidFrom n0) s) (ha : Absorbs s (lk θ)) (hT : ∀ a, a.isNew n = false → T a = s a) :
    FixesR (rigidFrom n0) T ∧ Absorbs T (lk θ) := by
  refine ⟨fun a hr => ?_, fun a => ?_⟩
  · have : a.isNew n = false := by
      cases e : a.isNew n
      · rfl
      · rw [not_rigid_of_new h0 e] at hr; cases hr
    rw [hT a this, hs a hr]
  · rcases hθ a with h1 | ⟨h1, h2⟩
    · rw [h1]; rfl
    · rw [hT a h1, ← ha a]
      apply sb_congr
      intro b hb
      obtain ⟨b', e, -, h4⟩ := h2 _ hb
      injection e with e; subst e; exact hT _ h4

/-- Agreement on the old variables of a type gives the same image. -/
theorem sb_agree {n : Nat} {τ : Ty} (hτ : OkT n τ) {s T : FSub} (hT : ∀ a, a.isNew n = false → T a = s a) :
    sb T τ = sb s τ :=
  sb_congr τ fun a ha => by obtain ⟨b, e, -, h⟩ := hτ _ ha; injection e with e; subst e; exact hT _ h

/-! ## Instantiation (L2) -/

theorem lk_zip_fresh : ∀ (as : List TyVar) (n : Nat) (a : TyVar),
    lk (as.zip (freshFrom n as)) a =
      if a ∈ as then .var (.fresh (n + as.idxOf a) a.cls) else .var a
  | [], _, _ => by simp [lk_nil]
  | b :: bs, n, a => by
    simp only [freshFrom, List.zip_cons_cons, lk_cons]
    by_cases e : b = a
    · subst e; simp
    · rw [if_neg e, lk_zip_fresh bs (n + 1) a]
      have hne : a ≠ b := fun h => e h.symm
      by_cases hm : a ∈ bs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        rw [List.idxOf_cons, if_neg (by simpa using e)]
        congr 2; omega
      · rw [if_neg hm, if_neg (by simp [hne, hm])]

theorem getD_idxOf {as : List TyVar} {a x : TyVar} (hm : a ∈ as) : as.getD (as.idxOf a) x = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm), Option.getD_some,
    List.getElem_idxOf]

/-- W's instance of a scheme over type variables is most general: every instance of `s σ` is an
    image of it, by a substitution agreeing with `s` outside W's new variables, and mapping each
    of them to an admissible type of its class. -/
theorem inst_exists {n : Nat} {σ : Scheme} {as : List TyVar} {s : FSub} {τ' : Ty}
    (hσ : SchW n σ) (hb : σ.bound = as.map BVar.ty) (hi : InstUnder s σ τ') :
    ∃ T : FSub, (∀ a, a.isNew n = false → T a = s a) ∧ (∀ a, a.isNew (n + as.length) = true → T a = s a) ∧
      (∀ a, T a ≠ s a → Adm a.cls (T a)) ∧
      sb T (sb (lk (as.zip (freshFrom n as))) σ.body) = τ' := by
  obtain ⟨g, hg, rfl⟩ := hi
  let T : FSub := fun a => match a with
    | .fresh k c =>
      if n ≤ k ∧ k < n + as.length ∧ c = (as.getD (k - n) a).cls then g (as.getD (k - n) a) else s a
    | a => s a
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro a ha
    match a, ha with
    | .fresh k c, ha =>
      simp only [TyVar.isNew, decide_eq_false_iff_not, Nat.not_le] at ha
      simp only [T]; rw [if_neg (by omega)]
    | .named _, _ => rfl
    | .bnd _ _, _ => rfl
  · intro a ha
    match a, ha with
    | .fresh k c, ha =>
      simp only [TyVar.isNew, decide_eq_true_eq] at ha
      simp only [T]; rw [if_neg (by omega)]
    | .named _, _ => rfl
    | .bnd _ _, _ => rfl
  · intro a ha
    match a, ha with
    | .fresh k c, ha =>
      simp only [T] at ha ⊢
      split at ha
      · rename_i h
        rw [if_pos h]
        obtain ⟨h1, h2, h3⟩ := h
        have hm : as.getD (k - n) (.fresh k c) ∈ as := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact List.getElem_mem _
        have hb' := hg _ (by rw [hb]; exact List.mem_map_of_mem hm)
        rw [← h3] at hb'
        exact hb'
      · exact absurd rfl ha
    | .named _, ha => exact absurd rfl ha
    | .bnd _ _, ha => exact absurd rfl ha
  · rw [sb_sb]
    apply sb_congr
    intro a ha
    simp only [comp, lk_zip_fresh, ext, hb, List.mem_map, BVar.ty.injEq, exists_eq_right]
    split
    · rename_i hm
      have hl := List.idxOf_lt_length_of_mem hm
      simp only [sb, T, Nat.add_sub_cancel_left, getD_idxOf hm]
      split
      · rfl
      · rename_i hc; exact absurd ⟨by omega, by omega, trivial⟩ hc
    · rename_i hm
      simp only [sb]
      obtain ⟨b, e, -, hold⟩ := hσ.2 _ ha (by rw [hb]; simpa using hm)
      injection e with e; subst e
      match a, hold with
      | .fresh k c, hold =>
        simp only [TyVar.isNew, decide_eq_false_iff_not, Nat.not_le] at hold
        simp only [T]; rw [if_neg (by omega)]
      | .named _, _ => rfl
      | .bnd _ _, _ => rfl

/-- W's instance is a type W builds. -/
theorem inst_okT {n : Nat} {σ : Scheme} {as : List TyVar} (hσ : SchW n σ) (hb : σ.bound = as.map BVar.ty) :
    OkT (n + as.length) (sb (lk (as.zip (freshFrom n as))) σ.body) := by
  intro v hv
  rcases vars_sb _ _ v hv with ⟨e, rfl, he⟩ | ⟨a, ha, hv'⟩
  · by_cases hm : BVar.row e ∈ σ.bound
    · rw [hb] at hm; simp at hm
    · obtain ⟨_, h, _⟩ := hσ.2 _ he hm; cases h
  · rw [lk_zip_fresh] at hv'
    split at hv'
    · rename_i hm
      simp only [Ty.vars, List.mem_singleton] at hv'
      subst hv'
      exact ⟨_, rfl, rfl, by simp [TyVar.isNew]; exact List.idxOf_lt_length_of_mem hm⟩
    · rename_i hm
      simp only [Ty.vars, List.mem_singleton] at hv'
      subst hv'
      obtain ⟨b, e, h1, h2⟩ := hσ.2 _ ha (by rw [hb]; simpa using hm)
      injection e with e; subst e
      exact ⟨_, rfl, h1, isNew_mono (Nat.le_add_right _ _) h2⟩

/-! ## The root context -/

theorem freshAbove_aux : ∀ (l : List BVar) (m : Nat),
    m ≤ l.foldl (fun m v => match v with
      | .ty (.fresh k _) => max m (k + 1)
      | _ => m) m ∧
    ∀ k c, BVar.ty (.fresh k c) ∈ l → k < l.foldl (fun m v => match v with
      | .ty (.fresh k _) => max m (k + 1)
      | _ => m) m
  | [], m => ⟨Nat.le_refl _, fun _ _ h => by cases h⟩
  | v :: l, m => by
    simp only [List.foldl_cons]
    have ih := freshAbove_aux l
    constructor
    · refine Nat.le_trans ?_ (ih _).1
      split <;> omega
    · intro k c hk
      rcases List.mem_cons.mp hk with e | hk
      · subst e
        simp only
        exact Nat.lt_of_lt_of_le (by omega) (ih _).1
      · exact (ih _).2 k c hk

theorem old_of_root {C0 : Ctx} {a : TyVar} (h : BVar.ty a ∈ C0.tyvars) : a.isNew (freshAbove C0) = false := by
  cases a with
  | fresh k c =>
    have := (freshAbove_aux (C0.tyvars ++ veAllVars C0.E.VE) 0).2 k c (List.mem_append_left _ h)
    simp only [TyVar.isNew, decide_eq_false_iff_not, Nat.not_le]
    exact this
  | _ => rfl

/-- A variable of a binding of the root context, shadowed or not, is not W's. -/
theorem old_of_root_ve {C0 : Ctx} {a : TyVar} {p : String × (Scheme × IdStatus)} (hp : p ∈ C0.E.VE)
    (h : BVar.ty a ∈ p.2.1.body.vars) : a.isNew (freshAbove C0) = false := by
  cases a with
  | fresh k c =>
    have := (freshAbove_aux (C0.tyvars ++ veAllVars C0.E.VE) 0).2 k c
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, h⟩))
    simp only [TyVar.isNew, decide_eq_false_iff_not, Nat.not_le]
    exact this
  | _ => rfl

theorem rigid_bnd (n0 i : Nat) (c : Cls) : rigidFrom n0 (.bnd i c) = true := rfl

/-- The root context is related to itself under a substitution fixing the rigid variables. -/
theorem root_rel {C0 : Ctx} {s : FSub} (hs : FixesR (rigidFrom (freshAbove C0)) s) :
    CtxRel (SchRel s) (rigidFrom (freshAbove C0)) C0 C0 := by
  refine ⟨rfl, rfl, rfl, rfl, fun x => ?_, fun a ha => rigid_of_old (old_of_root (mem_ctx_tyvars.mpr (.inl ha)))⟩
  cases hf : FMap.find? C0.E.VE x with
  | none => trivial
  | some p =>
    refine ⟨rfl, schRel_refl fun a ha hb => ?_⟩
    cases a with
    | bnd i c => exact hs _ rfl
    | _ =>
      apply hs
      apply rigid_of_old
      apply old_of_root
      refine mem_ctx_tyvars.mpr (.inr ⟨x, p, hf, ?_⟩)
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not]
      exact ⟨⟨ha, rfl⟩, hb⟩

/-- The schemes of the root context are schemes W can put in its contexts. -/
theorem root_ctxW {C0 : Ctx} (hC : RootOK C0) : CtxW (freshAbove C0) C0 := by
  intro lv σ st hl
  obtain ⟨h1, h2⟩ := hC lv σ st hl
  refine ⟨h1, fun v hv hb => ?_⟩
  obtain ⟨a, rfl, ha⟩ := h2 v hv hb
  refine ⟨a, rfl, by cases a <;> simp_all [BVar.isBnd, TyVar.isBndT], old_of_root ?_⟩
  have hfree : BVar.ty a ∈ σ.tyvars := by
    simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨⟨hv, ha⟩, hb⟩
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl
    exact mem_ctx_tyvars.mpr (.inr ⟨lv.id, (σ, st), hl, hfree⟩)
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl
    cases hI : FMap.find? C0.E.QE m with
    | none => rw [hI] at hl; cases hl
    | some I =>
      rw [hI] at hl
      simp only [Option.bind_some] at hl
      refine mem_ctx_tyvars.mpr (.inl ?_)
      simp only [restTv, List.mem_append]
      left; left
      rw [mem_tyvarsBy]
      refine ⟨m, I, by simp, hI, ?_⟩
      simp only [IEnv.tyvars, List.mem_append]
      right
      exact mem_VE_tyvars.mpr ⟨lv.id, (σ, st), hl, hfree⟩

end StandardElm.Stat.Complete
