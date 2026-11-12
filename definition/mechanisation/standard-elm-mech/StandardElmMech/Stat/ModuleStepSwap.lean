/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), first part: a
  bijection between two lists of type names, arity-preserving and outside `T0`, extends to a
  bijection of all type names (`NRInv`) that fixes every other name of a given list.

  Two families of disjoint swaps through fresh names: `aᵢ ↔ fᵢ`, then `fᵢ ↔ bᵢ`. Each family is an
  involution, so the composite has the other composite as inverse.
-/
import StandardElmMech.Stat.Ident

namespace StandardElm.Stat

namespace Swap

/-! ## A family of disjoint swaps -/

def swaps (P : List (TyName × TyName)) : List (TyName × TyName) := P ++ P.map fun p => (p.2, p.1)

theorem lookup_of_mem : ∀ {L : List (TyName × TyName)} {t y : TyName}, (L.map (·.1)).Nodup → (t, y) ∈ L →
    L.lookup t = some y
  | [], _, _, _, h => by simp at h
  | (a, b) :: rest, t, y, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.lookup]
    rcases List.mem_cons.mp h with e | e
    · cases e; simp
    · have : t ≠ a := fun e' => hn.1 (e' ▸ List.mem_map_of_mem (f := (·.1)) e)
      have hb : (t == a) = false := beq_eq_false_iff_ne.mpr this
      rw [hb]; exact lookup_of_mem hn.2 e

theorem lookup_none : ∀ {L : List (TyName × TyName)} {t : TyName}, t ∉ L.map (·.1) → L.lookup t = none
  | [], _, _ => rfl
  | (a, b) :: rest, t, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hb : (t == a) = false := beq_eq_false_iff_ne.mpr h.1
    simp only [List.lookup, hb]; exact lookup_none h.2

section
variable {P : List (TyName × TyName)} (hP : (P.map (·.1) ++ P.map (·.2)).Nodup)

include hP in
theorem swaps_keys : ((swaps P).map (·.1)).Nodup := by
  simpa [swaps, List.map_append, List.map_map, Function.comp_def] using hP

include hP in
theorem swaps_fst {p : TyName × TyName} (hp : p ∈ P) : (nr (swaps P)).tnApply p.1 = p.2 := by
  simp only [Renaming.tnApply, nr]
  rw [lookup_of_mem (swaps_keys hP) (List.mem_append_left _ hp)]; rfl

include hP in
theorem swaps_snd {p : TyName × TyName} (hp : p ∈ P) : (nr (swaps P)).tnApply p.2 = p.1 := by
  simp only [Renaming.tnApply, nr]
  rw [lookup_of_mem (swaps_keys hP) (List.mem_append_right _ (List.mem_map_of_mem (f := fun p : TyName × TyName => (p.2, p.1)) hp))]; rfl

theorem swaps_other (_hP : (P.map (·.1) ++ P.map (·.2)).Nodup) {t : TyName} (h1 : t ∉ P.map (·.1)) (h2 : t ∉ P.map (·.2)) : (nr (swaps P)).tnApply t = t := by
  simp only [Renaming.tnApply, nr]
  rw [lookup_none]; · rfl
  simp only [swaps, List.map_append, List.map_map, Function.comp_def, List.mem_append, not_or]
  exact ⟨h1, by simpa using h2⟩

theorem swaps_cases (_hP : (P.map (·.1) ++ P.map (·.2)).Nodup) (t : TyName) : (∃ p ∈ P, t = p.1) ∨ (∃ p ∈ P, t = p.2) ∨ (t ∉ P.map (·.1) ∧ t ∉ P.map (·.2)) := by
  by_cases h1 : t ∈ P.map (·.1)
  · obtain ⟨p, hp, e⟩ := List.mem_map.mp h1; exact .inl ⟨p, hp, e.symm⟩
  · by_cases h2 : t ∈ P.map (·.2)
    · obtain ⟨p, hp, e⟩ := List.mem_map.mp h2; exact .inr (.inl ⟨p, hp, e.symm⟩)
    · exact .inr (.inr ⟨h1, h2⟩)

include hP in
theorem swaps_invol (t : TyName) : (nr (swaps P)).tnApply ((nr (swaps P)).tnApply t) = t := by
  rcases swaps_cases hP t with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨h1, h2⟩
  · rw [swaps_fst hP hp, swaps_snd hP hp]
  · rw [swaps_snd hP hp, swaps_fst hP hp]
  · rw [swaps_other hP h1 h2, swaps_other hP h1 h2]

include hP in
theorem swaps_NR (har : ∀ p ∈ P, p.2.arity = p.1.arity) (h0 : ∀ p ∈ P, p.1 ∉ T0 ∧ p.2 ∉ T0) : NR (swaps P) where
  inj t u e := by rw [← swaps_invol hP t, e, swaps_invol hP u]
  ar t := by
    rcases swaps_cases hP t with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨h1, h2⟩
    · rw [swaps_fst hP hp, har p hp]
    · rw [swaps_snd hP hp, har p hp]
    · rw [swaps_other hP h1 h2]
  t0 t ht := by
    apply swaps_other hP
    · intro hm; obtain ⟨p, hp, e⟩ := List.mem_map.mp hm; exact (h0 p hp).1 (e ▸ ht)
    · intro hm; obtain ⟨p, hp, e⟩ := List.mem_map.mp hm; exact (h0 p hp).2 (e ▸ ht)

include hP in
theorem swaps_inv (har : ∀ p ∈ P, p.2.arity = p.1.arity) (h0 : ∀ p ∈ P, p.1 ∉ T0 ∧ p.2 ∉ T0) :
    NRInv (swaps P) (swaps P) :=
  ⟨swaps_NR hP har h0, swaps_NR hP har h0, swaps_invol hP, swaps_invol hP⟩

end

/-! ## Fresh names -/

def maxId : List TyName → Nat
  | [] => 0
  | t :: ts => max t.id (maxId ts)

theorem le_maxId : ∀ {l : List TyName} {t : TyName}, t ∈ l → t.id ≤ maxId l
  | [], _, h => by simp at h
  | u :: us, t, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [maxId]; omega
    · have := le_maxId h; simp only [maxId]; omega

/-- Each pair (a, b) with a fresh name of a's arity between. -/
def mkFresh : Nat → List (TyName × TyName) → List (TyName × TyName × TyName)
  | _, [] => []
  | n, p :: ps => (p.1, ⟨n, p.1.arity⟩, p.2) :: mkFresh (n + 1) ps

theorem mkFresh_fst : ∀ (n : Nat) (ps : List (TyName × TyName)), (mkFresh n ps).map (·.1) = ps.map (·.1)
  | _, [] => rfl
  | n, p :: ps => by simp [mkFresh, mkFresh_fst (n + 1) ps]

theorem mkFresh_trd : ∀ (n : Nat) (ps : List (TyName × TyName)), (mkFresh n ps).map (·.2.2) = ps.map (·.2)
  | _, [] => rfl
  | n, p :: ps => by simp [mkFresh, mkFresh_trd (n + 1) ps]

theorem mkFresh_pairs : ∀ (n : Nat) (ps : List (TyName × TyName)), (mkFresh n ps).map (fun x => (x.1, x.2.2)) = ps
  | _, [] => rfl
  | n, p :: ps => by simp [mkFresh, mkFresh_pairs (n + 1) ps]

theorem mkFresh_ge : ∀ (n : Nat) (ps : List (TyName × TyName)), ∀ x ∈ mkFresh n ps, n ≤ x.2.1.id
  | _, [], _, h => by simp [mkFresh] at h
  | n, p :: ps, x, h => by
    simp only [mkFresh, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mkFresh_ge (n + 1) ps x h; omega

theorem mkFresh_nodup : ∀ (n : Nat) (ps : List (TyName × TyName)), ((mkFresh n ps).map (·.2.1)).Nodup
  | _, [] => by simp [mkFresh]
  | n, p :: ps => by
    simp only [mkFresh, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun x hx e => ?_, mkFresh_nodup (n + 1) ps⟩
    have := mkFresh_ge (n + 1) ps x hx
    rw [e] at this; simp at this; omega

theorem mkFresh_mem : ∀ {n : Nat} {ps : List (TyName × TyName)}, ∀ x ∈ mkFresh n ps,
    (x.1, x.2.2) ∈ ps ∧ x.2.1.arity = x.1.arity
  | _, [], _, h => by simp [mkFresh] at h
  | n, p :: ps, x, h => by
    simp only [mkFresh, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := mkFresh_mem x h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem nodup_append_of {l1 l2 : List TyName} (h1 : l1.Nodup) (h2 : l2.Nodup) (hd : ∀ x ∈ l1, x ∉ l2) :
    (l1 ++ l2).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun a ha b hb e => hd a ha (e ▸ hb)⟩

/-- A bijection between two lists of names extends to a bijection of all type names that fixes
    every other name of `X`. -/
theorem extend_pairs (ν : List (TyName × TyName)) (h1 : (ν.map (·.1)).Nodup) (h2 : (ν.map (·.2)).Nodup)
    (har : ∀ p ∈ ν, p.2.arity = p.1.arity) (h0 : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0) (X : List TyName) :
    ∃ σ σ', NRInv σ σ' ∧ (∀ p ∈ ν, (nr σ).tnApply p.1 = p.2) ∧
      (∀ t ∈ X, t ∉ ν.map (·.1) → t ∉ ν.map (·.2) → (nr σ).tnApply t = t) := by
  let N := maxId (ν.map (·.1) ++ ν.map (·.2) ++ X ++ T0) + 1
  have hN : ∀ t ∈ ν.map (·.1) ++ ν.map (·.2) ++ X ++ T0, t.id < N := fun t ht => by
    have := le_maxId ht; omega
  let F := mkFresh N ν
  let P1 : List (TyName × TyName) := F.map fun x => (x.1, x.2.1)
  let P2 : List (TyName × TyName) := F.map fun x => (x.2.1, x.2.2)
  have hF := mkFresh_ge N ν
  have hfresh : ∀ x ∈ F, x.2.1 ∉ ν.map (·.1) ++ ν.map (·.2) ++ X ++ T0 := fun x hx hm => by
    have := hN _ hm; have := hF x hx; omega
  have e1 : P1.map (·.1) = ν.map (·.1) := by simp [P1, List.map_map, Function.comp_def, ← mkFresh_fst N ν, F]
  have e2 : P2.map (·.2) = ν.map (·.2) := by simp [P2, List.map_map, Function.comp_def, ← mkFresh_trd N ν, F]
  have ef1 : P1.map (·.2) = F.map (·.2.1) := by simp [P1, List.map_map, Function.comp_def]
  have ef2 : P2.map (·.1) = F.map (·.2.1) := by simp [P2, List.map_map, Function.comp_def]
  have hP1 : (P1.map (·.1) ++ P1.map (·.2)).Nodup := by
    rw [e1, ef1]
    refine nodup_append_of h1 (mkFresh_nodup N ν) fun a ha hb => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact hfresh x hx (by simp [ha])
  have hP2 : (P2.map (·.1) ++ P2.map (·.2)).Nodup := by
    rw [e2, ef2]
    refine nodup_append_of (mkFresh_nodup N ν) h2 fun a ha hb => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hfresh x hx (by simp [hb])
  have hT0 : ∀ x ∈ F, x.2.1 ∉ T0 := fun x hx hm => hfresh x hx (by simp [hm])
  have i1 : NRInv (swaps P1) (swaps P1) := swaps_inv hP1
    (fun p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact (mkFresh_mem x hx).2)
    (fun p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact ⟨fun h => (h0 _ (mkFresh_mem x hx).1).1 h, hT0 x hx⟩)
  have i2 : NRInv (swaps P2) (swaps P2) := swaps_inv hP2
    (fun p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hm, ha⟩ := mkFresh_mem x hx
      show x.2.2.arity = x.2.1.arity
      rw [ha]; exact har _ hm)
    (fun p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact ⟨hT0 x hx, fun h => (h0 _ (mkFresh_mem x hx).1).2 h⟩)
  refine ⟨nrComp (swaps P2) (swaps P1), nrComp (swaps P1) (swaps P2), i2.comp i1, ?_, ?_⟩
  · intro p hp
    -- p is the image of its entry of F
    have : p ∈ F.map fun x => (x.1, x.2.2) := by
      rw [mkFresh_pairs]; exact hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp this
    rw [nrComp_tn, swaps_fst hP1 (List.mem_map_of_mem (f := fun x => (x.1, x.2.1)) hx),
      swaps_fst hP2 (List.mem_map_of_mem (f := fun x => (x.2.1, x.2.2)) hx)]
  · intro t ht n1 n2
    have hf : t ∉ F.map (·.2.1) := fun hm => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      exact hfresh x hx (by simp [ht])
    rw [nrComp_tn, swaps_other hP1 (by rw [e1]; exact n1) (by rw [ef1]; exact hf),
      swaps_other hP2 (by rw [ef2]; exact hf) (by rw [e2]; exact n2)]

end Swap

end StandardElm.Stat
