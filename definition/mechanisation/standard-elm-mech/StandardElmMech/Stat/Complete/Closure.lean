/-
  A Standard Definition of Elm? Mechanisation: the generalisation lemma L3 of plan step 11
  (milestone (b), section 8), for the closure of a group (A93's `closGroup`, through `canon`'s
  renumbering).

  For a group environment of monotypes `VE` in a context with free variables `A`, and an
  instance `T` of it in a context with free variables `A'` such that the free variables of `T A`
  are in `A'` (`hA`), the closure of each member is related to the closure of its image
  (`closE_rel`): the free variables of `T (Clos_A τ)` are free in `Clos_A' (T τ)`, and every
  instance of `Clos_A' (T τ)` is an instance of `T (Clos_A τ)`. This is the book's L3,
  `T (Clos_C σ) ≻ Clos_{T C} (T σ)`, with A93's extra number variables (vacuous, they change no
  instance) and with `C'` any context whose free variables include those of `T C`.
-/
import StandardElmMech.Stat.Complete.Canon
import StandardElmMech.Stat.Complete.MguTerm

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## `renumber` -/

theorem renumber_spec (k : Bool) : ∀ (i : Nat) (vs : List BVar),
    RowRen (renumber k i vs).1 ∧ (∀ v ∈ (renumber k i vs).1.dom, v ∈ vs) ∧
      ∀ v ∈ (renumber k i vs).2, v.isBnd = true
  | _, [] => ⟨fun _ h => (by simp [renumber, Subst.id] at h),
      fun _ h => (by simp [renumber, Subst.id, Subst.dom] at h), fun _ h => (by simp [renumber] at h)⟩
  | i, .ty a :: vs => by
    obtain ⟨h1, h2, h3⟩ := renumber_spec k (i + 1) vs
    refine ⟨h1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [renumber, Subst.dom, List.map_cons, List.mem_append, List.mem_cons] at hv
      rcases hv with (rfl | hv) | hv
      · exact .head _
      · exact .tail _ (h2 v (by simp [Subst.dom, hv]))
      · exact .tail _ (h2 v (by simp [Subst.dom, hv]))
    · simp only [renumber, List.mem_cons] at hv
      rcases hv with rfl | hv
      · rfl
      · exact h3 v hv
  | i, .row e :: vs => by
    obtain ⟨h1, h2, h3⟩ := renumber_spec k (i + 1) vs
    refine ⟨fun p hp => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [renumber, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact h1 p hp
    · simp only [renumber, Subst.dom, List.map_cons, List.mem_append, List.mem_cons] at hv
      rcases hv with hv | (rfl | hv)
      · exact .tail _ (h2 v (by simp [Subst.dom, hv]))
      · exact .head _
      · exact .tail _ (h2 v (by simp [Subst.dom, hv]))
    · simp only [renumber, List.mem_cons] at hv
      rcases hv with rfl | hv
      · rfl
      · exact h3 v hv

/-- The renaming of a list of type variables to `bnd i, bnd (i+1), ...`. -/
def rnTy : Nat → List TyVar → Bnd
  | _, [] => []
  | i, a :: as => (a, .var (.bnd i a.cls)) :: rnTy (i + 1) as

def rnBs : Nat → List TyVar → List BVar
  | _, [] => []
  | i, a :: as => .ty (.bnd i a.cls) :: rnBs (i + 1) as

theorem renumber_ty : ∀ (i : Nat) (as : List TyVar),
    renumber true i (as.map BVar.ty) = (ofBnd (rnTy i as), rnBs i as)
  | _, [] => rfl
  | i, a :: as => by simp only [List.map_cons, renumber, renumber_ty (i + 1) as, ofBnd, rnTy, rnBs]; rfl

theorem lk_rnTy : ∀ (i : Nat) (as : List TyVar) (a : TyVar),
    lk (rnTy i as) a = if a ∈ as then .var (.bnd (i + as.idxOf a) a.cls) else .var a
  | _, [], _ => by simp [rnTy, lk_nil]
  | i, b :: bs, a => by
    simp only [rnTy, lk_cons]
    by_cases e : b = a
    · subst e; simp
    · rw [if_neg e, lk_rnTy (i + 1) bs a]
      have hne : a ≠ b := fun h => e h.symm
      by_cases hm : a ∈ bs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        rw [List.idxOf_cons, if_neg (by simpa using e)]
        have : i + 1 + bs.idxOf a = i + (bs.idxOf a + 1) := by omega
        rw [this]
      · rw [if_neg hm, if_neg (by simp [hne, hm])]

theorem mem_rnBs : ∀ (i : Nat) (as : List TyVar) (a : TyVar), a ∈ as →
    BVar.ty (.bnd (i + as.idxOf a) a.cls) ∈ rnBs i as
  | _, [], _, h => by cases h
  | i, b :: bs, a, h => by
    simp only [rnBs, List.mem_cons]
    by_cases e : b = a
    · subst e; simp
    · right
      rw [List.idxOf_cons, if_neg (by simpa using e)]
      have hm : a ∈ bs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      have := mem_rnBs (i + 1) bs a hm
      rw [show i + (List.idxOf a bs + 1) = i + 1 + List.idxOf a bs by omega]; exact this

theorem rnBs_cls : ∀ (i : Nat) (as : List TyVar) (j : Nat) (c : Cls), BVar.ty (.bnd j c) ∈ rnBs i as →
    i ≤ j ∧ j - i < as.length ∧ ∀ d, c = (as.getD (j - i) d).cls
  | _, [], _, _, h => by cases h
  | i, b :: bs, j, c, h => by
    simp only [rnBs, List.mem_cons, BVar.ty.injEq, TyVar.bnd.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · obtain ⟨h1, h2, h3⟩ := rnBs_cls (i + 1) bs j c h
      refine ⟨by omega, by simp; omega, fun d => ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using h3 d

theorem rnBs_bnd : ∀ (i : Nat) (as : List TyVar), ∀ v ∈ rnBs i as, ∃ j c, v = .ty (.bnd j c)
  | _, [], _, h => by cases h
  | i, b :: bs, v, h => by
    simp only [rnBs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, _, rfl⟩
    · exact rnBs_bnd (i + 1) bs v h

/-! ## `canonVars` and `canon` -/

theorem mem_canonVars {bound : List BVar} {body : Ty} {v : BVar} (h : v ∈ canonVars bound body) : v ∈ bound := by
  simp only [canonVars, List.mem_append, mem_dedupL, List.mem_filter, decide_eq_true_eq] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact h

theorem mem_canonVars_iff {bound : List BVar} {body : Ty} {v : BVar} (hv : v ∈ body.vars) :
    v ∈ canonVars bound body ↔ v ∈ bound := by
  refine ⟨mem_canonVars, fun h => ?_⟩
  simp only [canonVars, List.mem_append, mem_dedupL, List.mem_filter, decide_eq_true_eq]
  exact .inl ⟨hv, h⟩

theorem list_ty_of {l : List BVar} (h : ∀ v ∈ l, ∃ a, v = .ty a) : ∃ as : List TyVar, l = as.map BVar.ty := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons v l ih =>
    obtain ⟨a, rfl⟩ := h v (.head _)
    obtain ⟨as, rfl⟩ := ih (fun w hw => h w (.tail _ hw))
    exact ⟨a :: as, rfl⟩

/-- The canonical form of a scheme whose bound variables are type variables: a renaming of the
    occurring ones (and of the vacuous ones of class num) to `bnd 0, bnd 1, ...`. -/
theorem canon_ty {bound : List BVar} {body : Ty} (h : ∀ v ∈ bound, ∃ a, v = .ty a) :
    ∃ as : List TyVar, canonVars bound body = as.map BVar.ty ∧
      Scheme.canon ⟨bound, body⟩ = ⟨rnBs 0 as, sb (lk (rnTy 0 as)) body⟩ := by
  obtain ⟨as, has⟩ := list_ty_of (fun v hv => h v (mem_canonVars hv))
  refine ⟨as, has, ?_⟩
  simp only [Scheme.canon, has, renumber_ty, apply_ofBnd, Option.getD_some]

/-- The free variables of a scheme's canonical form include those of the scheme. -/
theorem mem_canon_tyvars {σ : Scheme} {v : BVar} (hv : v ∈ σ.body.tyvars) (hb : v ∉ σ.bound) :
    v ∈ (Scheme.canon σ).tyvars := by
  obtain ⟨h1, h2, h3⟩ := renumber_spec true 0 (canonVars σ.bound σ.body)
  have hvb : v ∈ σ.body.vars ∧ v.isBnd = false := by
    simp only [Ty.tyvars, List.mem_filter, Bool.not_eq_true'] at hv; exact hv
  have hd : v ∉ (renumber true 0 (canonVars σ.bound σ.body)).1.dom := fun h => hb (mem_canonVars (h2 v h))
  obtain ⟨τ', hτ'⟩ := apply_isSome h1 σ.body
  simp only [Scheme.canon, hτ', Option.getD_some, Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter,
    Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨⟨apply_keeps h1 _ _ hτ' v hvb.1 hd, hvb.2⟩, fun h => ?_⟩
  rw [h3 v h] at hvb; cases hvb.2

/-! ## Step 9's bindings -/

theorem bindSubst_dom : ∀ {vs : List BVar} {ts : List Ty} {S : Subst}, bindSubst vs ts = some S →
    ∀ v ∈ S.dom, v ∈ vs
  | [], [], S, h => by simp only [bindSubst, Option.some.injEq] at h; subst h; simp [Subst.id, Subst.dom]
  | .ty a :: vs, τ :: ts, S, h => by
    simp only [bindSubst] at h
    cases hb : bindSubst vs ts with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h
      intro v hv
      simp only [Subst.dom, List.map_cons, List.mem_append, List.mem_cons] at hv
      rcases hv with (rfl | hv) | hv
      · exact .head _
      · exact .tail _ (bindSubst_dom hb v (by simp [Subst.dom, hv]))
      · exact .tail _ (bindSubst_dom hb v (by simp [Subst.dom, hv]))
  | .row e :: vs, .record ρ tl :: ts, S, h => by
    simp only [bindSubst] at h
    cases hb : bindSubst vs ts with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h
      intro v hv
      simp only [Subst.dom, List.map_cons, List.mem_append, List.mem_cons] at hv
      rcases hv with hv | (rfl | hv)
      · exact .tail _ (bindSubst_dom hb v (by simp [Subst.dom, hv]))
      · exact .head _
      · exact .tail _ (bindSubst_dom hb v (by simp [Subst.dom, hv]))
  | [], _ :: _, _, h => by simp [bindSubst] at h
  | _ :: _, [], _, h => by cases ‹BVar› <;> simp [bindSubst] at h
  | .row _ :: _, .var _ :: _, _, h => by simp [bindSubst] at h
  | .row _ :: _, .fn _ _ :: _, _, h => by simp [bindSubst] at h
  | .row _ :: _, .con _ _ :: _, _, h => by simp [bindSubst] at h

/-! ## The closure of a group's member -/

/-- The bound list of the closure `closGroup` gives a member with scheme `σ` (A93). -/
def closB (A : List BVar) (VE : ValEnv) (σ : Scheme) : List BVar :=
  σ.bound ++ diffL (dedupL σ.tyvars) A ++
    (diffL (dedupL (ValEnv.tyvars VE)) (σ.tyvars ++ A)).filter BVar.isNumTyVar

/-- The closure `closGroup` gives a member with scheme `σ`. -/
def closE (A : List BVar) (VE : ValEnv) (σ : Scheme) : Scheme := Scheme.canon ⟨closB A VE σ, σ.body⟩

theorem closGroup_eq (A : List BVar) (VE : ValEnv) : closGroup A VE = VE.mapV fun p => (closE A VE p.1, p.2) := rfl

theorem find?_closGroup (A : List BVar) (VE : ValEnv) (x : String) :
    FMap.find? (closGroup A VE) x = (FMap.find? VE x).map fun p => (closE A VE p.1, p.2) := by
  rw [closGroup_eq]; exact find?_mapVW _ VE x

theorem mono_tyvars (τ : Ty) : (mono τ).tyvars = τ.tyvars := by
  simp [Scheme.tyvars, mono, diffL]

@[simp] theorem mono_bound (τ : Ty) : (mono τ).bound = [] := rfl
@[simp] theorem mono_body (τ : Ty) : (mono τ).body = τ := rfl

theorem mem_tyvars_iff {v : BVar} {τ : Ty} : v ∈ τ.tyvars ↔ v ∈ τ.vars ∧ v.isBnd = false := by
  simp [Ty.tyvars]

/-- The bound list of a member's closure: its free variables outside `A`, then number variables. -/
theorem closE_bound_ty {A : List BVar} {VE : ValEnv} {τ : Ty} (hτ : TyOnly τ) :
    ∀ v ∈ closB A VE (mono τ), ∃ a, v = .ty a := by
  intro v hv
  simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL] at hv
  rcases hv with ⟨hv, _⟩ | ⟨_, hv⟩
  · exact hτ v (mem_tyvars_iff.mp hv).1
  · cases v with
    | ty a => exact ⟨a, rfl⟩
    | row e => simp [BVar.isNumTyVar] at hv

/-- L3 for a member of a group: the closure in W's context is related to the closure of its
    image in the derivation's context. -/
theorem closE_rel {A A' : List BVar} {VE VE' : ValEnv} {τ : Ty} {T : FSub} {n : Nat}
    (hτ : OkT n τ) (hTadm : RespC T)
    (hA : ∀ a, BVar.ty a ∈ A → BVar.ty a ∈ τ.vars → ∀ v ∈ (T a).tyvars, v ∈ A')
    (hNB : ∀ v ∈ (sb T τ).vars, v.isBnd = false) :
    SchRel T (closE A VE (mono τ)) (closE A' VE' (mono (sb T τ))) := by
  have hto : TyOnly τ := TyOnly.of_okT hτ
  obtain ⟨as, hcv, hc⟩ := canon_ty (body := τ) (closE_bound_ty (A := A) (VE := VE) hto)
  -- a variable of τ outside the bound list is in A
  have inA : ∀ c, BVar.ty c ∈ τ.vars → c ∉ as → BVar.ty c ∈ A := by
    intro c hc hn
    have hnb : BVar.ty c ∉ List.map BVar.ty as := by simpa using hn
    rw [← hcv, mem_canonVars_iff hc] at hnb
    obtain ⟨c', e, hb, -⟩ := hτ _ hc
    injection e with e; subst e
    refine Classical.byContradiction fun hA' => ?_
    apply hnb
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
      mem_tyvars_iff, decide_eq_false_iff_not, Bool.not_eq_true']
    refine .inl ⟨⟨hc, ?_⟩, hA'⟩
    cases c <;> simp_all [BVar.isBnd, TyVar.isBndT]
  -- the images under T of variables in A are fixed by the derivation's renaming and instance
  have hfix : ∀ c, BVar.ty c ∈ τ.vars → BVar.ty c ∈ A → ∀ v ∈ (T c).vars,
      v ∉ closB A' VE' (mono (sb T τ)) ∧ v.isBnd = false := by
    intro c hc hcA v hv
    have hnb : v.isBnd = false := hNB v (vars_sb_of T τ c v hc hv)
    have hA'v : v ∈ A' := hA c hcA hc v (mem_tyvars_iff.mpr ⟨hv, hnb⟩)
    refine ⟨?_, hnb⟩
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
      decide_eq_false_iff_not, Bool.not_eq_true', not_or, not_and, List.mem_append]
    exact ⟨fun _ h => h hA'v, fun h => absurd hA'v h.2.2⟩
  refine ⟨?_, ?_⟩
  · -- FtvRel
    intro a ha v hv
    unfold closE at ha
    rw [mono_body, hc] at ha
    simp only [Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
      decide_eq_false_iff_not] at ha
    obtain ⟨⟨ha1, ha2⟩, -⟩ := ha
    obtain ⟨c, hc', hac⟩ := tyvar_sb ha1
    rw [lk_rnTy] at hac
    split at hac
    · simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hac; subst hac; cases ha2
    · rename_i hn
      simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hac; subst hac
      have hcA := inA _ hc' hn
      unfold closE
      apply mem_canon_tyvars (σ := ⟨_, (mono (sb T τ)).body⟩)
      · have hv' := mem_tyvars_iff.mp hv
        exact mem_tyvars_iff.mpr ⟨vars_sb_of T τ _ v hc' hv'.1, hv'.2⟩
      · exact (hfix _ hc' hcA v (mem_tyvars_iff.mp hv).1).1
  · -- every instance of the image's closure is an instance of the closure under T
    intro _ t hg
    unfold closE at hg
    simp only [Scheme.canon, mono_body] at hg
    obtain ⟨h1, h2, h3⟩ := renumber_spec true 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ))
    have hRN := renumber_respectsC 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ))
    generalize renumber true 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ)) = RN at hg h1 h2 h3 hRN
    obtain ⟨β, hβ⟩ := apply_isSome h1 (sb T τ)
    obtain ⟨ts, S2, hS2, hr2, ht⟩ := hg
    rw [hβ, Option.getD_some] at ht
    obtain ⟨k1, k2⟩ := apply_sb _ T τ β hto hβ
    subst k2
    obtain ⟨k3, k4⟩ := apply_sb _ _ τ t hto ht
    subst k4
    -- on the variables in A, the composite is T
    have hpost : ∀ c, BVar.ty c ∈ τ.vars → BVar.ty c ∈ A → post S2 (post RN.1 T) c = T c := by
      intro c hc hcA
      have e1 : RN.1.apply (T c) = some (T c) := apply_fix _ _ fun v hv hd =>
        (hfix c hc hcA v hv).1 (mem_canonVars (h2 v hd))
      have e2 : S2.apply (T c) = some (T c) := apply_fix _ _ fun v hv hd => by
        have := h3 v (bindSubst_dom hS2 v hd)
        rw [(hfix c hc hcA v hv).2] at this; cases this
      simp only [post, e1, Option.getD_some, e2]
    let h := post S2 (post RN.1 T)
    refine ⟨fun b => match b with
      | .bnd j _ => if j < as.length then h (as.getD j b) else .var b
      | b => .var b, ?_, ?_⟩
    · intro a ha
      unfold closE at ha
      rw [mono_body, hc] at ha
      obtain ⟨j, cl, e⟩ := rnBs_bnd 0 as _ ha
      injection e with e; subst e
      obtain ⟨-, h2, h3⟩ := rnBs_cls 0 as j cl ha
      simp only [Nat.sub_zero] at h2 h3
      simp only [if_pos h2]
      have := admC_post hr2 (admC_post hRN (hTadm (as.getD j (.bnd j cl))))
      rw [← h3 (.bnd j cl)] at this
      exact this
    unfold closE
    rw [mono_body, hc, sb_sb]
    apply sb_congr
    intro c hcv
    simp only [comp, lk_rnTy]
    split
    · rename_i hm
      simp only [sb, ext, Nat.zero_add]
      have hm' := mem_rnBs 0 as c hm
      simp only [Nat.zero_add] at hm'
      rw [if_pos hm', if_pos (List.idxOf_lt_length_of_mem hm), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm), Option.getD_some, List.getElem_idxOf]
    · rename_i hm
      simp only [sb, ext]
      have hnb : BVar.ty c ∉ rnBs 0 as := by
        intro hb
        obtain ⟨j, cl, e⟩ := rnBs_bnd 0 as _ hb
        injection e with e; subst e
        obtain ⟨c', e', hb', -⟩ := hτ _ hcv
        injection e' with e'; subst e'; cases hb'
      rw [if_neg hnb]
      exact hpost c hcv (inA c hcv hm)

/-- The closure of a member is a scheme W can put in its context. -/
theorem closE_schW {A : List BVar} {VE : ValEnv} {τ : Ty} {n : Nat} (hτ : OkT n τ) :
    SchW n (closE A VE (mono τ)) := by
  obtain ⟨as, _, hc⟩ := canon_ty (body := τ) (closE_bound_ty (A := A) (VE := VE) (TyOnly.of_okT hτ))
  unfold closE; rw [mono_body, hc]
  refine ⟨fun v hv => by obtain ⟨j, c, rfl⟩ := rnBs_bnd 0 as v hv; rfl, fun v hv hb => ?_⟩
  obtain ⟨c, hc', hv'⟩ := vars_sb _ τ v hv |>.resolve_left (by
    rintro ⟨e, rfl, he⟩; obtain ⟨_, h, _⟩ := hτ _ he; cases h)
  rw [lk_rnTy] at hv'
  split at hv'
  · rename_i hm
    simp only [Ty.vars, List.mem_singleton] at hv'; subst hv'
    exact absurd (mem_rnBs 0 as c hm) (by simpa using hb)
  · simp only [Ty.vars, List.mem_singleton] at hv'; subst hv'
    exact hτ _ hc'

end StandardElm.Stat.Complete
