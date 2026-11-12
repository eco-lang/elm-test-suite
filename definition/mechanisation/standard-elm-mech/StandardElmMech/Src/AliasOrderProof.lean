/-
  A Standard Definition of Elm? Mechanisation: the canonical order of a module's aliases is one the
  book allows, plan step 8 (section 3.3): when no alias mentions itself through the others
  (res:modules-alias-not-recursive) and their names are distinct (res:modules-types-distinct),
  `aliasOrder` is a permutation in which each alias comes after every alias it mentions
  (`aliasOrder_valid`). Among the aliases not yet placed one may always come next: one whose count
  of reachable unplaced aliases is least (a step to an unplaced alias would reach strictly fewer,
  since no alias reaches itself).
-/
import StandardElmMech.Src.Derive
import StandardElmMech.Src.GroupingProof

namespace StandardElm.Src
open StandardElm.Src.Graph StandardElm.Src.Grouping

abbrev AliasD := String × List String × STy

variable {all : List AliasD}

/-- Alias i mentions alias j. -/
def mentionsIdx (all : List AliasD) (i j : Nat) : Bool :=
  match all[i]?, all[j]? with
  | some a, some b => mentions all a.2.2 b.1
  | _, _ => false

/-- The book's relation: a permutation in which each alias comes after the aliases it mentions. -/
def ValidAliasOrder (all order : List AliasD) : Prop :=
  order.Perm all ∧ ∀ i j (hi : i < order.length) (hj : j < order.length), i ≠ j →
    mentions all order[i].2.2 order[j].1 = true → j < i

/-- An alias may come next when every alias it mentions (other than itself) is placed. -/
def aReady (all placed : List AliasD) (a : AliasD) : Bool :=
  all.all fun b => b.1 == a.1 || !(mentions all a.2.2 b.1) || placed.any (·.1 == b.1)

theorem aliasOrderAux_eq (k : Nat) (placed rest : List AliasD) :
    aliasOrderAux all (k + 1) placed rest =
      match rest.find? (aReady all placed) with
      | some a => aliasOrderAux all k (placed ++ [a]) (rest.filter (·.1 != a.1))
      | none => placed ++ rest := rfl

/-- The index of an alias of a list with distinct names. -/
theorem exists_idx {a : AliasD} (h : a ∈ all) : ∃ i, ∃ hi : i < all.length, all[i] = a :=
  List.getElem_of_mem h

/-- A name-distinct list: removing an alias by name removes exactly it. -/
theorem perm_filter_name : ∀ {l : List AliasD} {a : AliasD}, (l.map (·.1)).Nodup → a ∈ l →
    l.Perm (a :: l.filter (·.1 != a.1))
  | [], _, _, h => by simp at h
  | b :: l, a, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · have hf : l.filter (·.1 != a.1) = l := by
        apply List.filter_eq_self.mpr
        intro x hx
        have : x.1 ≠ a.1 := fun he => hn.1 (he ▸ List.mem_map_of_mem hx)
        simpa using this
      simp [hf]
    · have hne : b.1 ≠ a.1 := fun he => hn.1 (he ▸ List.mem_map_of_mem h)
      have hb : (b.1 != a.1) = true := by simpa using hne
      simp only [List.filter_cons, hb, ite_true]
      exact ((perm_filter_name hn.2 h).cons b).trans (List.Perm.swap a b _)

theorem names_distinct {l : List AliasD} (h : (l.map (·.1)).Nodup) :
    ∀ i j (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i].1 ≠ l[j].1 := by
  intro i j hi hj hij he
  have hp := List.pairwise_iff_getElem.mp h
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact hp i j (by simpa using hi) (by simpa using hj) hlt (by simpa using he)
  · exact hp j i (by simpa using hj) (by simpa using hi) hlt (by simpa using he.symm)

/-- The count of unplaced aliases reachable from alias i by one or more steps. -/
def aCnt (all rest : List AliasD) (i : Nat) : Nat :=
  ((List.range all.length).filter fun j =>
    decide ((all[j]?.map (·.1)) ∈ rest.map (fun x => some x.1)) && plusB all.length (mentionsIdx all) i j).length

theorem exists_aReady {placed rest : List AliasD} (hp : (placed ++ rest).Perm all)
    (hnd : (all.map (·.1)).Nodup)
    (hacyc : ∀ i < all.length, ¬ Plus all.length (mentionsIdx all) i i) (hne : rest ≠ []) :
    ∃ a ∈ rest, aReady all placed a = true := by
  have hmemall : ∀ x ∈ rest, x ∈ all := fun x hx => hp.mem_iff.mp (List.mem_append_right _ hx)
  -- the indices of the unplaced aliases
  let idxs : List Nat := (List.range all.length).filter fun j =>
    decide ((all[j]?.map (·.1)) ∈ rest.map (fun x => some x.1))
  have hidx : ∀ x ∈ rest, ∃ i, ∃ hi : i < all.length, all[i] = x ∧ i ∈ idxs := by
    intro x hx
    obtain ⟨i, hi, he⟩ := exists_idx (hmemall x hx)
    refine ⟨i, hi, he, List.mem_filter.mpr ⟨List.mem_range.mpr hi, ?_⟩⟩
    simp only [decide_eq_true_eq, List.getElem?_eq_getElem hi, Option.map_some, he, List.mem_map]
    exact ⟨x, hx, rfl⟩
  obtain ⟨x1, hx1⟩ := List.exists_mem_of_ne_nil rest hne
  obtain ⟨i1, _, _, hi1⟩ := hidx x1 hx1
  have hne' : idxs ≠ [] := fun h => by rw [h] at hi1; simp at hi1
  obtain ⟨i0, hi0, hmin⟩ := exists_min (aCnt all rest) idxs hne'
  obtain ⟨hi0r, hi0p⟩ := List.mem_filter.mp hi0
  have hi0n : i0 < all.length := List.mem_range.mp hi0r
  simp only [decide_eq_true_eq, List.getElem?_eq_getElem hi0n, Option.map_some, List.mem_map,
    Option.some.injEq] at hi0p
  obtain ⟨a0, ha0, hname⟩ := hi0p
  -- a0 and all[i0] have one name, so are one alias
  have heq : all[i0] = a0 := by
    obtain ⟨j, hj, hje⟩ := exists_idx (hmemall a0 ha0)
    have : j = i0 := by
      apply Classical.byContradiction
      intro hji
      exact names_distinct hnd j i0 hj hi0n hji (by rw [hje]; exact hname)
    subst this; exact hje
  refine ⟨a0, ha0, ?_⟩
  unfold aReady
  apply List.all_eq_true.mpr
  intro b hb
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true]
  by_cases hbn : b.1 = a0.1
  · exact .inl (.inl hbn)
  cases hm : mentions all a0.2.2 b.1
  · exact .inl (.inr rfl)
  by_cases hbp : ∃ x ∈ placed, x.1 = b.1
  · exact .inr hbp
  exfalso
  -- b is unplaced
  have hbrest : b ∈ rest := by
    rcases List.mem_append.mp (hp.mem_iff.mpr hb) with h | h
    · exact absurd ⟨b, h, rfl⟩ hbp
    · exact h
  obtain ⟨ib, hib, hibe, hibi⟩ := hidx b hbrest
  have hstep : mentionsIdx all i0 ib = true := by
    simp [mentionsIdx, List.getElem?_eq_getElem hi0n, List.getElem?_eq_getElem hib, heq, hibe, hm]
  have hplus : Plus all.length (mentionsIdx all) i0 ib := .step hi0n hib hstep
  have hmono : ∀ y ∈ List.range all.length,
      (decide ((all[y]?.map (·.1)) ∈ rest.map (fun x => some x.1)) && plusB all.length (mentionsIdx all) ib y) = true →
      (decide ((all[y]?.map (·.1)) ∈ rest.map (fun x => some x.1)) && plusB all.length (mentionsIdx all) i0 y) = true := by
    intro y _ hy
    simp only [Bool.and_eq_true, plusB_iff] at hy ⊢
    exact ⟨hy.1, .trans hplus hy.2⟩
  have hle := len_filter_mono hmono
  have hne2 : aCnt all rest ib ≠ aCnt all rest i0 := by
    intro he
    have := len_filter_eq hmono he ib (List.mem_range.mpr hib)
      (by simp only [Bool.and_eq_true, plusB_iff]; exact ⟨(List.mem_filter.mp hibi).2, hplus⟩)
    simp only [Bool.and_eq_true, plusB_iff] at this
    exact hacyc ib hib this.2
  have := hmin ib hibi
  unfold aCnt at hle hne2 this
  omega

/-- Each alias of the list may come next after the ones before it. -/
def AReadyList (all : List AliasD) : List AliasD → List AliasD → Prop
  | _, [] => True
  | P, a :: as => aReady all P a = true ∧ AReadyList all (P ++ [a]) as

theorem aliasOrderAux_spec (hnd : (all.map (·.1)).Nodup)
    (hacyc : ∀ i < all.length, ¬ Plus all.length (mentionsIdx all) i i) :
    ∀ (k : Nat) (placed rest : List AliasD), (placed ++ rest).Perm all → rest.length ≤ k →
      ∃ out, aliasOrderAux all k placed rest = placed ++ out ∧ out.Perm rest ∧ AReadyList all placed out
  | 0, placed, rest, _, hk => by
    have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], by simp [aliasOrderAux], List.Perm.refl _, trivial⟩
  | k + 1, placed, rest, hp, hk => by
    by_cases hne : rest = []
    · subst hne
      exact ⟨[], by simp [aliasOrderAux], List.Perm.refl _, trivial⟩
    obtain ⟨c, hc, hrd⟩ := exists_aReady hp hnd hacyc hne
    rw [aliasOrderAux_eq]
    cases hf : rest.find? (aReady all placed) with
    | none => exact absurd hrd (List.find?_eq_none.mp hf c hc)
    | some a =>
      simp only
      have ha := List.mem_of_find?_eq_some hf
      have hready := List.find?_some hf
      have hndr : (rest.map (·.1)).Nodup := by
        have := (hp.map (·.1)).nodup_iff.mpr hnd
        simp only [List.map_append] at this
        exact (List.nodup_append.mp this).2.1
      have hperm := perm_filter_name hndr ha
      have hperm2 : ((placed ++ [a]) ++ rest.filter (·.1 != a.1)).Perm all := by
        rw [List.append_assoc]; exact (List.Perm.append_left _ hperm.symm).trans hp
      have hlen : (rest.filter (·.1 != a.1)).length ≤ k := by
        have := hperm.length_eq; simp at this; omega
      obtain ⟨out, hout, hpo, hrl⟩ := aliasOrderAux_spec hnd hacyc k (placed ++ [a]) _ hperm2 hlen
      refine ⟨a :: out, ?_, (hpo.cons a).trans hperm.symm, ⟨hready, hrl⟩⟩
      rw [hout]; simp

theorem aReadyList_get : ∀ (P os : List AliasD), AReadyList all P os →
    ∀ (k : Nat) (hk : k < os.length), aReady all (P ++ os.take k) os[k] = true
  | _, [], _, k, hk => by simp at hk
  | P, a :: os, ⟨h1, _⟩, 0, _ => by simpa using h1
  | P, a :: os, ⟨_, h2⟩, k + 1, hk => by
    have := aReadyList_get (P ++ [a]) os h2 k (by simp at hk; omega)
    simpa using this

theorem aliasOrder_valid (hnd : (all.map (·.1)).Nodup)
    (hacyc : ∀ i < all.length, ¬ Plus all.length (mentionsIdx all) i i) :
    ValidAliasOrder all (aliasOrder all) := by
  obtain ⟨out, hout, hp, hrl⟩ := aliasOrderAux_spec hnd hacyc all.length [] all (by simp) (Nat.le_refl _)
  have heq : aliasOrder all = out := by unfold aliasOrder; simpa using hout
  rw [heq]
  refine ⟨hp, ?_⟩
  intro i j hi hj hij hm
  have hndo : (out.map (·.1)).Nodup := (hp.map (·.1)).nodup_iff.mpr hnd
  have hdistinct := names_distinct hndo
  have hrd := aReadyList_get [] out hrl i hi
  simp only [List.nil_append] at hrd
  unfold aReady at hrd
  have hb := (List.all_eq_true.mp hrd) out[j] (hp.mem_iff.mp (List.getElem_mem hj))
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true, hm] at hb
  rcases hb with (he | hf) | ⟨x, hx, hxe⟩
  · exact absurd he (hdistinct j i hj hi (Ne.symm hij))
  · cases hf
  · obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hx
    have hk' := Nat.lt_min.mp hk
    have : k = j := by
      apply Classical.byContradiction
      intro hkj
      exact hdistinct k j hk'.2 hj hkj hxe
    subst this
    exact hk'.1

end StandardElm.Src
