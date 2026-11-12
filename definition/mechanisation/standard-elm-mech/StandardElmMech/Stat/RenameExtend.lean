/-
  A Standard Definition of Elm? Mechanisation: an injective map on finitely many variables extends
  to a renaming (plan step 10, `mutualInstanceMod_renaming`, the step "S is an injective
  class-preserving variable renaming").

  Given a finite list `V` of variables and a map `f` injective and class-preserving on `V`, never
  producing a bound variable, `extTv V f` agrees with `f` on `V` and is injective and
  class-preserving everywhere: the images `f V` not in `V` are sent to fresh variables above every
  index in sight, and the fresh variables there are shifted up to make room. Likewise for row
  variables (`extRv`).
-/
import StandardElmMech.Stat.RenameReduce

namespace StandardElm.Stat

/-! ## Positions in a list -/

def idxIn {α : Type} [DecidableEq α] : List α → α → Option Nat
  | [], _ => none
  | y :: ys, x => if y = x then some 0 else (idxIn ys x).map (· + 1)

theorem idxIn_none {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, idxIn l x = none ↔ x ∉ l
  | [] => by simp [idxIn]
  | y :: ys => by
    simp only [idxIn, List.mem_cons]
    by_cases h : y = x
    · subst h; simp
    · simp only [h, ↓reduceIte, Option.map_eq_none_iff, idxIn_none]
      constructor
      · intro hn hc; rcases hc with e | e
        · exact h e.symm
        · exact hn e
      · intro hn e; exact hn (.inr e)

theorem idxIn_lt {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α} {i : Nat}, idxIn l x = some i → i < l.length
  | [], _, h => by simp [idxIn] at h
  | y :: ys, i, h => by
    simp only [idxIn] at h
    split at h
    · cases h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := idxIn_lt hj
      simp only [List.length_cons]; omega

theorem idxIn_inj {α : Type} [DecidableEq α] {x x' : α} : ∀ {l : List α} {i : Nat},
    idxIn l x = some i → idxIn l x' = some i → x = x'
  | [], _, h, _ => by simp [idxIn] at h
  | y :: ys, i, h, h' => by
    simp only [idxIn] at h h'
    split at h <;> split at h'
    · rename_i e e'; exact e.symm.trans e'
    · cases h; obtain ⟨j, _, hj⟩ := Option.map_eq_some_iff.mp h'; omega
    · cases h'; obtain ⟨j, _, hj⟩ := Option.map_eq_some_iff.mp h; omega
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨j', hj', e⟩ := Option.map_eq_some_iff.mp h'
      have : j' = j := by omega
      subst this
      exact idxIn_inj hj hj'

/-! ## Type variables -/

def TyVar.freshIdx : TyVar → Nat
  | .fresh n _ => n
  | _ => 0

def maxFreshT : List TyVar → Nat
  | [] => 0
  | a :: as => max a.freshIdx (maxFreshT as)

theorem le_maxFreshT {a : TyVar} : ∀ {l : List TyVar}, a ∈ l → a.freshIdx ≤ maxFreshT l
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [List.mem_cons] at h
    simp only [maxFreshT]
    rcases h with rfl | h
    · omega
    · have := le_maxFreshT h; omega

/-- The extension of `f` from `V`. -/
def extTv (V : List TyVar) (f : TyVar → TyVar) (a : TyVar) : TyVar :=
  if a ∈ V then f a else
    match idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a with
    | some i => .fresh (maxFreshT (V ++ V.map f) + 1 + i) a.cls
    | none =>
      match a with
      | .fresh n c =>
        if maxFreshT (V ++ V.map f) + 1 ≤ n then .fresh (n + (dedupL ((V.map f).filter fun b => b ∉ V)).length) c
        else .fresh n c
      | a => a

section
variable (V : List TyVar) (f : TyVar → TyVar)

/-- The four cases of `extTv`. -/
theorem extTv_cases (a : TyVar) :
    (a ∈ V ∧ extTv V f a = f a) ∨
    (a ∉ V ∧ ∃ i, idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = some i ∧
      extTv V f a = .fresh (maxFreshT (V ++ V.map f) + 1 + i) a.cls) ∨
    (a ∉ V ∧ idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = none ∧ ∃ n c, a = .fresh n c ∧
      maxFreshT (V ++ V.map f) + 1 ≤ n ∧
      extTv V f a = .fresh (n + (dedupL ((V.map f).filter fun b => b ∉ V)).length) c) ∨
    (a ∉ V ∧ idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = none ∧
      (∀ n c, a = .fresh n c → n < maxFreshT (V ++ V.map f) + 1) ∧ extTv V f a = a) := by
  unfold extTv
  by_cases hV : a ∈ V
  · exact .inl ⟨hV, by simp [hV]⟩
  · rw [ite_cond_eq_false _ _ (eq_false hV)]
    cases hi : idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a with
    | some i => exact .inr (.inl ⟨hV, i, rfl, rfl⟩)
    | none =>
      cases a with
      | fresh n c =>
        by_cases hn : maxFreshT (V ++ V.map f) + 1 ≤ n
        · exact .inr (.inr (.inl ⟨hV, rfl, n, c, rfl, hn, by simp [hn]⟩))
        · refine .inr (.inr (.inr ⟨hV, rfl, ?_, by simp [hn]⟩))
          intro n' c' e; cases e; omega
      | named s => refine .inr (.inr (.inr ⟨hV, rfl, ?_, rfl⟩)); intro _ _ e; cases e
      | bnd i c => refine .inr (.inr (.inr ⟨hV, rfl, ?_, rfl⟩)); intro _ _ e; cases e

theorem extTv_inj (hinj : ∀ a ∈ V, ∀ b ∈ V, f a = f b → a = b) : ∀ a b, extTv V f a = extTv V f b → a = b := by
  intro a b h
  have hfV : ∀ x ∈ V, ∀ n c, f x = .fresh n c → n < maxFreshT (V ++ V.map f) + 1 := by
    intro x hx n c e
    have := le_maxFreshT (a := f x) (l := V ++ V.map f) (List.mem_append_right _ (List.mem_map_of_mem hx))
    rw [e] at this; simp only [TyVar.freshIdx] at this; omega
  have hW : ∀ x ∈ V, f x ∉ V → f x ∈ dedupL ((V.map f).filter fun b => b ∉ V) := by
    intro x hx hn
    exact mem_dedupL.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem hx, by simpa using hn⟩)
  rcases extTv_cases V f a with ⟨ha, ea⟩ | ⟨ha, i, hi, ea⟩ | ⟨ha, hi, n, c, rfl, hn, ea⟩ | ⟨ha, hi, hn, ea⟩ <;>
  rcases extTv_cases V f b with ⟨hb, eb⟩ | ⟨hb, j, hj, eb⟩ | ⟨hb, hj, m, d, rfl, hm, eb⟩ | ⟨hb, hj, hm, eb⟩ <;>
  rw [ea, eb] at h
  · exact hinj a ha b hb h
  · have := hfV a ha _ _ h; omega
  · have := hfV a ha _ _ h; omega
  · -- f a = b with b outside V and outside W
    subst h
    have := hW a ha hb
    rw [idxIn_none] at hj; exact absurd this hj
  · have := hfV b hb _ _ h.symm; omega
  · simp only [TyVar.fresh.injEq] at h
    have : i = j := by omega
    subst this; exact idxIn_inj hi hj
  · simp only [TyVar.fresh.injEq] at h
    have := idxIn_lt hi; omega
  · have := hm _ _ h.symm; omega
  · have := hfV b hb _ _ h.symm; omega
  · simp only [TyVar.fresh.injEq] at h
    have := idxIn_lt hj; omega
  · simp only [TyVar.fresh.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : n = m := by omega
    subst this; subst h2; rfl
  · have := hm _ _ h.symm; omega
  · subst h
    have := hW b hb ha
    rw [idxIn_none] at hi; exact absurd this hi
  · have := hn _ _ h; omega
  · have := hn _ _ h; omega
  · exact h

theorem extTv_cls (hcls : ∀ a ∈ V, (f a).cls = a.cls) (a : TyVar) : (extTv V f a).cls = a.cls := by
  rcases extTv_cases V f a with ⟨ha, ea⟩ | ⟨_, i, _, ea⟩ | ⟨_, _, n, c, rfl, _, ea⟩ | ⟨_, _, _, ea⟩ <;> rw [ea]
  · exact hcls a ha
  · rfl
  · rfl

theorem extTv_bnd (hbV : ∀ a ∈ V, ∀ i c, a ≠ .bnd i c) (hbf : ∀ a ∈ V, ∀ i c, f a ≠ .bnd i c) (i : Nat) (c : Cls) :
    extTv V f (.bnd i c) = .bnd i c := by
  rcases extTv_cases V f (.bnd i c) with ⟨ha, _⟩ | ⟨_, j, hj, _⟩ | ⟨_, _, n, d, e, _, _⟩ | ⟨_, _, _, ea⟩
  · exact absurd rfl (hbV _ ha i c)
  · have := (Option.isSome_iff_exists.mpr ⟨j, hj⟩)
    rw [← Option.ne_none_iff_isSome, ne_eq, idxIn_none, Decidable.not_not, mem_dedupL] at this
    obtain ⟨hm, _⟩ := List.mem_filter.mp this
    obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
    exact absurd e (hbf x hx i c)
  · cases e
  · exact ea

theorem extTv_on (a : TyVar) (ha : a ∈ V) : extTv V f a = f a := by simp [extTv, ha]

end

/-! ## Row variables -/

def RowVar.freshIdx : RowVar → Nat
  | .fresh n => n
  | _ => 0

def maxFreshR : List RowVar → Nat
  | [] => 0
  | a :: as => max a.freshIdx (maxFreshR as)

theorem le_maxFreshR {a : RowVar} : ∀ {l : List RowVar}, a ∈ l → a.freshIdx ≤ maxFreshR l
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [List.mem_cons] at h
    simp only [maxFreshR]
    rcases h with rfl | h
    · omega
    · have := le_maxFreshR h; omega

def extRv (V : List RowVar) (f : RowVar → RowVar) (a : RowVar) : RowVar :=
  if a ∈ V then f a else
    match idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a with
    | some i => .fresh (maxFreshR (V ++ V.map f) + 1 + i)
    | none =>
      match a with
      | .fresh n =>
        if maxFreshR (V ++ V.map f) + 1 ≤ n then .fresh (n + (dedupL ((V.map f).filter fun b => b ∉ V)).length)
        else .fresh n
      | a => a

section
variable (V : List RowVar) (f : RowVar → RowVar)

theorem extRv_cases (a : RowVar) :
    (a ∈ V ∧ extRv V f a = f a) ∨
    (a ∉ V ∧ ∃ i, idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = some i ∧
      extRv V f a = .fresh (maxFreshR (V ++ V.map f) + 1 + i)) ∨
    (a ∉ V ∧ idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = none ∧ ∃ n, a = .fresh n ∧
      maxFreshR (V ++ V.map f) + 1 ≤ n ∧
      extRv V f a = .fresh (n + (dedupL ((V.map f).filter fun b => b ∉ V)).length)) ∨
    (a ∉ V ∧ idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a = none ∧
      (∀ n, a = .fresh n → n < maxFreshR (V ++ V.map f) + 1) ∧ extRv V f a = a) := by
  unfold extRv
  by_cases hV : a ∈ V
  · exact .inl ⟨hV, by simp [hV]⟩
  · rw [ite_cond_eq_false _ _ (eq_false hV)]
    cases hi : idxIn (dedupL ((V.map f).filter fun b => b ∉ V)) a with
    | some i => exact .inr (.inl ⟨hV, i, rfl, rfl⟩)
    | none =>
      cases a with
      | fresh n =>
        by_cases hn : maxFreshR (V ++ V.map f) + 1 ≤ n
        · exact .inr (.inr (.inl ⟨hV, rfl, n, rfl, hn, by simp [hn]⟩))
        · refine .inr (.inr (.inr ⟨hV, rfl, ?_, by simp [hn]⟩))
          intro n' e; cases e; omega
      | named s => refine .inr (.inr (.inr ⟨hV, rfl, ?_, rfl⟩)); intro _ e; cases e
      | bnd i => refine .inr (.inr (.inr ⟨hV, rfl, ?_, rfl⟩)); intro _ e; cases e

theorem extRv_inj (hinj : ∀ a ∈ V, ∀ b ∈ V, f a = f b → a = b) : ∀ a b, extRv V f a = extRv V f b → a = b := by
  intro a b h
  have hfV : ∀ x ∈ V, ∀ n, f x = .fresh n → n < maxFreshR (V ++ V.map f) + 1 := by
    intro x hx n e
    have := le_maxFreshR (a := f x) (l := V ++ V.map f) (List.mem_append_right _ (List.mem_map_of_mem hx))
    rw [e] at this; simp only [RowVar.freshIdx] at this; omega
  have hW : ∀ x ∈ V, f x ∉ V → f x ∈ dedupL ((V.map f).filter fun b => b ∉ V) := by
    intro x hx hn
    exact mem_dedupL.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem hx, by simpa using hn⟩)
  rcases extRv_cases V f a with ⟨ha, ea⟩ | ⟨ha, i, hi, ea⟩ | ⟨ha, hi, n, rfl, hn, ea⟩ | ⟨ha, hi, hn, ea⟩ <;>
  rcases extRv_cases V f b with ⟨hb, eb⟩ | ⟨hb, j, hj, eb⟩ | ⟨hb, hj, m, rfl, hm, eb⟩ | ⟨hb, hj, hm, eb⟩ <;>
  rw [ea, eb] at h
  · exact hinj a ha b hb h
  · have := hfV a ha _ h; omega
  · have := hfV a ha _ h; omega
  · subst h
    have := hW a ha hb
    rw [idxIn_none] at hj; exact absurd this hj
  · have := hfV b hb _ h.symm; omega
  · simp only [RowVar.fresh.injEq] at h
    have : i = j := by omega
    subst this; exact idxIn_inj hi hj
  · simp only [RowVar.fresh.injEq] at h
    have := idxIn_lt hi; omega
  · have := hm _ h.symm; omega
  · have := hfV b hb _ h.symm; omega
  · simp only [RowVar.fresh.injEq] at h
    have := idxIn_lt hj; omega
  · simp only [RowVar.fresh.injEq] at h
    have : n = m := by omega
    subst this; rfl
  · have := hm _ h.symm; omega
  · subst h
    have := hW b hb ha
    rw [idxIn_none] at hi; exact absurd this hi
  · have := hn _ h; omega
  · have := hn _ h; omega
  · exact h

theorem extRv_bnd (hbV : ∀ a ∈ V, ∀ i, a ≠ .bnd i) (hbf : ∀ a ∈ V, ∀ i, f a ≠ .bnd i) (i : Nat) :
    extRv V f (.bnd i) = .bnd i := by
  rcases extRv_cases V f (.bnd i) with ⟨ha, _⟩ | ⟨_, j, hj, _⟩ | ⟨_, _, n, e, _, _⟩ | ⟨_, _, _, ea⟩
  · exact absurd rfl (hbV _ ha i)
  · have := (Option.isSome_iff_exists.mpr ⟨j, hj⟩)
    rw [← Option.ne_none_iff_isSome, ne_eq, idxIn_none, Decidable.not_not, mem_dedupL] at this
    obtain ⟨hm, _⟩ := List.mem_filter.mp this
    obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
    exact absurd e (hbf x hx i)
  · cases e
  · exact ea

theorem extRv_on (a : RowVar) (ha : a ∈ V) : extRv V f a = f a := by simp [extRv, ha]

end

/-- The renaming that extends maps on finitely many variables, with a finite map on type names. -/
def extRenaming (Vt : List TyVar) (ft : TyVar → TyVar) (Vr : List RowVar) (fr : RowVar → RowVar)
    (tn : List (TyName × TyName)) : Renaming :=
  ⟨extTv Vt ft, extRv Vr fr, tn⟩

theorem extRenaming_wf {Vt : List TyVar} {ft : TyVar → TyVar} {Vr : List RowVar} {fr : RowVar → RowVar}
    {tn : List (TyName × TyName)}
    (ht_inj : ∀ a ∈ Vt, ∀ b ∈ Vt, ft a = ft b → a = b) (ht_cls : ∀ a ∈ Vt, (ft a).cls = a.cls)
    (ht_bV : ∀ a ∈ Vt, ∀ i c, a ≠ .bnd i c) (ht_bf : ∀ a ∈ Vt, ∀ i c, ft a ≠ .bnd i c)
    (hr_inj : ∀ a ∈ Vr, ∀ b ∈ Vr, fr a = fr b → a = b)
    (hr_bV : ∀ a ∈ Vr, ∀ i, a ≠ .bnd i) (hr_bf : ∀ a ∈ Vr, ∀ i, fr a ≠ .bnd i)
    (htn : ∀ p ∈ tn, p.1 ∉ T0 ∧ p.2 ∉ T0) :
    (extRenaming Vt ft Vr fr tn).WF where
  tv_inj := extTv_inj Vt ft ht_inj
  tv_cls := extTv_cls Vt ft ht_cls
  tv_bnd := extTv_bnd Vt ft ht_bV ht_bf
  rv_inj := extRv_inj Vr fr hr_inj
  rv_bnd := extRv_bnd Vr fr hr_bV hr_bf
  tn_T0 := by
    intro t t0 h0
    simp only [Renaming.tnApply, extRenaming]
    cases hl : tn.lookup t with
    | none => simp
    | some t' =>
      simp only [Option.getD_some]
      have hm : (t, t') ∈ tn := by
        induction tn with
        | nil => simp [List.lookup] at hl
        | cons p ps ih =>
          obtain ⟨k, v⟩ := p
          simp only [List.lookup] at hl
          by_cases hk : t = k
          · subst hk; simp at hl; subst hl; exact List.mem_cons_self ..
          · have : (t == k) = false := beq_eq_false_iff_ne.mpr hk
            simp only [this] at hl
            exact List.mem_cons_of_mem _ (ih (fun p hp => htn p (List.mem_cons_of_mem _ hp)) hl)
      obtain ⟨h1, h2⟩ := htn _ hm
      constructor
      · intro e; subst e; exact absurd h0 h2
      · intro e; subst e; exact absurd h0 h1

end StandardElm.Stat
