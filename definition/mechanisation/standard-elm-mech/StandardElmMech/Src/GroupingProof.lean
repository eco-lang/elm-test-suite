/-
  A Standard Definition of Elm? Mechanisation: the canonical grouping is one the book allows,
  plan step 8 (section 3.3, finding B4): `components_valid : ValidNumbering n r (components n r)`.

  The classes are the equivalence classes of mutual reachability, each sorted, covering
  `0 .. n-1` without overlap. They are placed in an order in which each comes after the classes its
  members refer to: among the classes not yet placed one is always ready, because a node whose
  count of reachable unplaced nodes is least lies in a ready class (a step out of its class to an
  unplaced class would reach strictly fewer nodes, since the way back is closed).
-/
import StandardElmMech.Src.Grouping

namespace StandardElm.Src.Grouping
open StandardElm.Src.Graph

variable {n : Nat} {r : Nat → Nat → Bool}

/-! ## Mutual reachability -/

theorem reach_refl (a : Nat) : Reach n r a a := .inl rfl

theorem reach_trans {a b c : Nat} (h1 : Reach n r a b) (h2 : Reach n r b c) : Reach n r a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact .inr h1
    · exact .inr (.trans h1 h2)

theorem reach_step {a b : Nat} (ha : a < n) (hb : b < n) (h : r a b = true) : Reach n r a b :=
  .inr (.step ha hb h)

/-- Mutual reachability. -/
def MR (n : Nat) (r : Nat → Nat → Bool) (a b : Nat) : Prop := Reach n r a b ∧ Reach n r b a

theorem mr_refl (a : Nat) : MR n r a a := ⟨reach_refl a, reach_refl a⟩
theorem mr_symm {a b : Nat} (h : MR n r a b) : MR n r b a := ⟨h.2, h.1⟩
theorem mr_trans {a b c : Nat} (h1 : MR n r a b) (h2 : MR n r b c) : MR n r a c :=
  ⟨reach_trans h1.1 h2.1, reach_trans h2.2 h1.2⟩

/-! ## The reach table -/

theorem reachIn_iff {a b : Nat} (ha : a < n) : reachIn (reachTable n r) a b = true ↔ Reach n r a b := by
  unfold reachIn reachTable
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]
  simp only [Option.map_some, Option.getD_some, List.contains_cons]
  rw [Bool.or_eq_true, beq_iff_eq, ← plusB, plusB_iff]
  simp only [Reach]
  constructor
  · rintro (h | h)
    · exact .inl h.symm
    · exact .inr h
  · rintro (h | h)
    · exact .inl h.symm
    · exact .inr h

/-- The class of a. -/
def cls (n : Nat) (r : Nat → Nat → Bool) (a : Nat) : List Nat :=
  (List.range n).filter (fun b => reachIn (reachTable n r) a b && reachIn (reachTable n r) b a)

theorem mem_cls {a b : Nat} (ha : a < n) : b ∈ cls n r a ↔ b < n ∧ MR n r a b := by
  unfold cls
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hb, h⟩
    rw [Bool.and_eq_true, reachIn_iff ha, reachIn_iff hb] at h
    exact ⟨hb, h⟩
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    rw [Bool.and_eq_true, reachIn_iff ha, reachIn_iff hb]
    exact h

theorem self_mem_cls {a : Nat} (ha : a < n) : a ∈ cls n r a := (mem_cls ha).mpr ⟨ha, mr_refl a⟩

theorem cls_sorted (a : Nat) : (cls n r a).Pairwise (· < ·) := by
  unfold cls
  exact (List.pairwise_lt_range).filter _

/-! ## The classes partition `range n` -/

def Disj (c d : List Nat) : Prop := ∀ x ∈ c, x ∉ d

theorem disj_symm {c d : List Nat} (h : Disj c d) : Disj d c := fun x hd hc => h x hc hd

/-- The invariant of the classes built so far: each is the class of some node, and they do not
    overlap. -/
def Inv (n : Nat) (r : Nat → Nat → Bool) (acc : List (List Nat)) : Prop :=
  (∀ c ∈ acc, ∃ a, a < n ∧ c = cls n r a) ∧ acc.Pairwise Disj

def stepC (n : Nat) (r : Nat → Nat → Bool) (acc : List (List Nat)) (a : Nat) : List (List Nat) :=
  if acc.any (fun cmp => cmp.contains a) then acc else acc ++ [cls n r a]

theorem classes_eq : classes n r = (List.range n).foldl (stepC n r) [] := rfl

theorem stepC_inv {acc : List (List Nat)} {a : Nat} (ha : a < n) (h : Inv n r acc) :
    Inv n r (stepC n r acc a) ∧ (∀ x c, c ∈ acc → x ∈ c → ∃ c' ∈ stepC n r acc a, x ∈ c') ∧
      (∃ c ∈ stepC n r acc a, a ∈ c) ∧ (stepC n r acc a).length ≤ acc.length + 1 := by
  unfold stepC
  split
  · rename_i hin
    obtain ⟨c, hc, ha'⟩ := List.any_eq_true.mp hin
    exact ⟨h, fun x c hc hx => ⟨c, hc, hx⟩, ⟨c, hc, List.contains_iff_mem.mp ha'⟩, by omega⟩
  · rename_i hnin
    have hnot : ∀ c ∈ acc, a ∉ c := by
      intro c hc hac
      exact hnin (List.any_eq_true.mpr ⟨c, hc, List.contains_iff_mem.mpr hac⟩)
    refine ⟨⟨?_, ?_⟩, fun x c hc hx => ⟨c, List.mem_append_left _ hc, hx⟩,
      ⟨_, List.mem_append_right _ (List.mem_singleton_self _), self_mem_cls ha⟩, by simp⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h.1 c hc
      · rw [List.mem_singleton.mp hc]; exact ⟨a, ha, rfl⟩
    · apply List.pairwise_append.mpr
      refine ⟨h.2, List.pairwise_singleton _ _, ?_⟩
      intro c hc d hd x hxc hxd
      rw [List.mem_singleton.mp hd] at hxd
      obtain ⟨a', ha', rfl⟩ := h.1 c hc
      have h1 := (mem_cls ha').mp hxc
      have h2 := (mem_cls ha).mp hxd
      have : a ∈ cls n r a' := (mem_cls ha').mpr ⟨ha, mr_trans h1.2 (mr_symm h2.2)⟩
      exact hnot _ hc this

theorem foldl_inv : ∀ (l : List Nat) (acc : List (List Nat)), (∀ a ∈ l, a < n) → Inv n r acc →
    Inv n r (l.foldl (stepC n r) acc) ∧
      (∀ x, ((∃ c ∈ acc, x ∈ c) ∨ x ∈ l) → ∃ c ∈ l.foldl (stepC n r) acc, x ∈ c) ∧
      (l.foldl (stepC n r) acc).length ≤ acc.length + l.length
  | [], acc, _, h => ⟨h, fun x hx => by simpa using hx, by simp⟩
  | a :: l, acc, hl, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := stepC_inv (r := r) (hl a List.mem_cons_self) h
    obtain ⟨i1, i2, i3⟩ := foldl_inv l (stepC n r acc a) (fun b hb => hl b (List.mem_cons_of_mem _ hb)) h1
    refine ⟨i1, ?_, by simp only [List.length_cons] at *; omega⟩
    intro x hx
    apply i2
    rcases hx with ⟨c, hc, hxc⟩ | hx
    · exact .inl (h2 x c hc hxc)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inl h3
      · exact .inr hx

theorem classes_inv : Inv n r (classes n r) := by
  rw [classes_eq]
  exact (foldl_inv (List.range n) [] (fun a ha => List.mem_range.mp ha) ⟨by simp, List.Pairwise.nil⟩).1

theorem classes_cover {x : Nat} (hx : x < n) : ∃ c ∈ classes n r, x ∈ c := by
  rw [classes_eq]
  exact (foldl_inv (List.range n) [] (fun a ha => List.mem_range.mp ha) ⟨by simp, List.Pairwise.nil⟩).2.1 x
    (.inr (List.mem_range.mpr hx))

theorem classes_length : (classes n r).length ≤ n := by
  rw [classes_eq]
  have := (foldl_inv (r := r) (List.range n) [] (fun a ha => List.mem_range.mp ha) ⟨by simp, List.Pairwise.nil⟩).2.2
  simpa using this

/-! ## Among the unplaced classes one is ready -/

def Cover (n : Nat) (all : List (List Nat)) : Prop := ∀ x, x < n → ∃ c ∈ all, x ∈ c

/-- The count of unplaced nodes reachable from x. -/
def cnt (n : Nat) (r : Nat → Nat → Bool) (T : List Nat) (x : Nat) : Nat :=
  ((List.range n).filter (fun y => decide (y ∈ T) && reachB n r x y)).length

theorem exists_min (f : Nat → Nat) : ∀ (l : List Nat), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, f x ≤ f y
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨x, hx, hm⟩ := exists_min f (b :: l) (by simp)
    by_cases h : f a ≤ f x
    · refine ⟨a, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_trans h (hm y hy)
    · refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hm y hy

theorem cls_lt {a x : Nat} (ha : a < n) (hx : x ∈ cls n r a) : x < n := ((mem_cls ha).mp hx).1

theorem exists_ready {placed todo : List (List Nat)} (hinv : Inv n r (placed ++ todo))
    (hcov : Cover n (placed ++ todo)) (hne : todo ≠ []) : ∃ c ∈ todo, ready n r placed c = true := by
  have hcls : ∀ c ∈ todo, ∃ a, a < n ∧ c = cls n r a := fun c hc => hinv.1 c (List.mem_append_right _ hc)
  obtain ⟨c1, rest, htodo⟩ : ∃ c rest, todo = c :: rest := by
    cases todo with
    | nil => exact absurd rfl hne
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc1mem : c1 ∈ todo := by rw [htodo]; exact List.mem_cons_self
  obtain ⟨a1, ha1, hc1⟩ := hcls c1 hc1mem
  have hTne : todo.flatten ≠ [] := by
    intro h
    have : a1 ∈ todo.flatten := List.mem_flatten.mpr ⟨c1, hc1mem, by rw [hc1]; exact self_mem_cls ha1⟩
    rw [h] at this; simp at this
  obtain ⟨x0, hx0, hmin⟩ := exists_min (cnt n r todo.flatten) todo.flatten hTne
  obtain ⟨c0, hc0, hx0c⟩ := List.mem_flatten.mp hx0
  obtain ⟨a0, ha0, rfl⟩ := hcls c0 hc0
  refine ⟨cls n r a0, hc0, ?_⟩
  unfold ready
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hbn : b < n := List.mem_range.mp hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.contains_iff_mem]
  cases hr : r a b
  · exact .inl (.inl rfl)
  by_cases hbc : b ∈ cls n r a0
  · exact .inl (.inr hbc)
  by_cases hbp : ∃ p ∈ placed, b ∈ p
  · exact .inr hbp
  exfalso
  obtain ⟨c, hc, hbc'⟩ := hcov b hbn
  have hcT : c ∈ todo := by
    rcases List.mem_append.mp hc with hc | hc
    · exact absurd ⟨c, hc, hbc'⟩ hbp
    · exact hc
  have hbT : b ∈ todo.flatten := List.mem_flatten.mpr ⟨c, hcT, hbc'⟩
  have hx := (mem_cls ha0).mp hx0c
  have haa := (mem_cls ha0).mp ha
  have hxb : Reach n r x0 b := reach_trans (mr_trans (mr_symm hx.2) haa.2).1 (reach_step haa.1 hbn hr)
  have hnb : ¬ Reach n r b x0 := fun h => hbc ((mem_cls ha0).mpr ⟨hbn, mr_trans hx.2 ⟨hxb, h⟩⟩)
  have hmono : ∀ y ∈ List.range n, (decide (y ∈ todo.flatten) && reachB n r b y) = true →
      (decide (y ∈ todo.flatten) && reachB n r x0 y) = true := by
    intro y _ hy
    simp only [Bool.and_eq_true, decide_eq_true_eq, reachB_iff] at hy ⊢
    exact ⟨hy.1, reach_trans hxb hy.2⟩
  have hle := len_filter_mono hmono
  have hne' : cnt n r todo.flatten b ≠ cnt n r todo.flatten x0 := by
    intro heq
    have := len_filter_eq hmono heq x0 (List.mem_range.mpr hx.1)
      (by simp only [Bool.and_eq_true, decide_eq_true_eq, reachB_iff]; exact ⟨hx0, reach_refl x0⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, reachB_iff] at this
    exact hnb this.2
  have := hmin b hbT
  unfold cnt at hle hne' this
  omega

/-! ## Placing -/

/-- Each class of the list is ready with respect to the classes before it. -/
def ReadyList (n : Nat) (r : Nat → Nat → Bool) : List (List Nat) → List (List Nat) → Prop
  | _, [] => True
  | P, c :: cs => ready n r P c = true ∧ ReadyList n r (P ++ [c]) cs

theorem inv_nonempty {all : List (List Nat)} (h : Inv n r all) : ∀ c ∈ all, c ≠ [] := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := h.1 c hc
  intro he
  have := self_mem_cls (r := r) ha
  rw [he] at this; simp at this

theorem inv_nodup {all : List (List Nat)} (h : Inv n r all) : all.Nodup := by
  have hne := inv_nonempty h
  refine List.Pairwise.imp_of_mem (R := Disj) ?_ h.2
  intro c d hc _ hcd he
  subst he
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil c (hne c hc)
  exact hcd x hx hx

theorem inv_perm {l1 l2 : List (List Nat)} (hp : l1.Perm l2) (h : Inv n r l1) : Inv n r l2 :=
  ⟨fun c hc => h.1 c (hp.mem_iff.mpr hc), (hp.pairwise_iff (fun {_ _} => disj_symm)).mp h.2⟩

theorem cover_perm {l1 l2 : List (List Nat)} (hp : l1.Perm l2) (h : Cover n l1) : Cover n l2 :=
  fun x hx => let ⟨c, hc, hxc⟩ := h x hx; ⟨c, hp.mem_iff.mp hc, hxc⟩

theorem place_spec : ∀ (k : Nat) (placed todo : List (List Nat)), Inv n r (placed ++ todo) →
    Cover n (placed ++ todo) → todo.length ≤ k →
    ∃ out, place n r k placed todo = placed ++ out ∧ out.Perm todo ∧ ReadyList n r placed out
  | 0, placed, todo, _, _, hk => by
    have : todo = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], by simp [place], List.Perm.refl _, trivial⟩
  | k + 1, placed, todo, hinv, hcov, hk => by
    by_cases hne : todo = []
    · subst hne
      exact ⟨[], by simp [place], List.Perm.refl _, trivial⟩
    obtain ⟨c, hc, hrd⟩ := exists_ready hinv hcov hne
    cases hf : todo.find? (ready n r placed) with
    | none => exact absurd hrd (List.find?_eq_none.mp hf c hc)
    | some cmp =>
      have hcmp := List.mem_of_find?_eq_some hf
      have hready := List.find?_some hf
      have hnd : todo.Nodup := (List.nodup_append.mp (inv_nodup hinv)).2.1
      have hperm : todo.Perm (cmp :: todo.filter (· != cmp)) := by
        rw [← hnd.erase_eq_filter]; exact List.perm_cons_erase hcmp
      have hperm2 : (placed ++ todo).Perm ((placed ++ [cmp]) ++ todo.filter (· != cmp)) := by
        rw [List.append_assoc]; exact List.Perm.append_left _ hperm
      have hlen : (todo.filter (· != cmp)).length ≤ k := by
        have := hperm.length_eq; simp at this; omega
      obtain ⟨out, hout, hp, hrl⟩ := place_spec k (placed ++ [cmp]) (todo.filter (· != cmp))
        (inv_perm hperm2 hinv) (cover_perm hperm2 hcov) hlen
      refine ⟨cmp :: out, ?_, ?_, ⟨hready, hrl⟩⟩
      · simp only [place, hf]; rw [hout]; simp
      · exact (hp.cons cmp).trans hperm.symm

theorem readyList_get : ∀ (P cs : List (List Nat)), ReadyList n r P cs →
    ∀ (k : Nat) (hk : k < cs.length), ready n r (P ++ cs.take k) cs[k] = true
  | _, [], _, k, hk => by simp at hk
  | P, c :: cs, ⟨h1, h2⟩, 0, _ => by simpa using h1
  | P, c :: cs, ⟨_, h2⟩, k + 1, hk => by
    have := readyList_get (P ++ [c]) cs h2 k (by simp at hk; omega)
    simpa using this

/-! ## The canonical grouping is valid -/

theorem flatten_nodup : ∀ (L : List (List Nat)), (∀ l ∈ L, l.Nodup) → L.Pairwise Disj → L.flatten.Nodup
  | [], _, _ => List.nodup_nil
  | c :: L, h1, h2 => by
    simp only [List.flatten_cons]
    rw [List.pairwise_cons] at h2
    apply List.nodup_append.mpr
    refine ⟨h1 c List.mem_cons_self, flatten_nodup L (fun l hl => h1 l (List.mem_cons_of_mem _ hl)) h2.2, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨d, hd, had⟩ := List.mem_flatten.mp hb
    exact h2.1 d hd a ha had

theorem components_valid (n : Nat) (r : Nat → Nat → Bool) : ValidNumbering n r (components n r) := by
  have hinv : Inv n r ([] ++ classes n r) := by simpa using classes_inv
  have hcov : Cover n ([] ++ classes n r) := fun x hx => by simpa using classes_cover (r := r) hx
  obtain ⟨cs, hcs, hp, hrl⟩ := place_spec (n := n) (r := r) (n + 1) [] (classes n r) hinv hcov
    (Nat.le_trans classes_length (Nat.le_succ n))
  have heq : components n r = cs := by unfold components; simpa using hcs
  rw [heq]
  have hcls : ∀ c ∈ cs, ∃ a, a < n ∧ c = cls n r a := fun c hc => classes_inv.1 c (hp.mem_iff.mp hc)
  have hdisj : cs.Pairwise Disj := (hp.pairwise_iff (fun {_ _} => disj_symm)).mpr classes_inv.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the classes partition range n
    apply (List.perm_ext_iff_of_nodup _ List.nodup_range).mpr
    · intro x
      rw [List.mem_range, List.mem_flatten]
      constructor
      · rintro ⟨c, hc, hx⟩
        obtain ⟨a, ha, rfl⟩ := hcls c hc
        exact cls_lt ha hx
      · intro hx
        obtain ⟨c, hc, hxc⟩ := classes_cover (r := r) hx
        exact ⟨c, hp.mem_iff.mpr hc, hxc⟩
    · apply flatten_nodup cs _ hdisj
      intro c hc
      obtain ⟨a, _, rfl⟩ := hcls c hc
      exact (cls_sorted a).imp (fun h => Nat.ne_of_lt h)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := hcls c hc
    refine ⟨cls_sorted a, fun he => ?_⟩
    have := self_mem_cls (r := r) ha
    rw [he] at this; simp at this
  · intro c hc i hi j hj
    obtain ⟨a, ha, rfl⟩ := hcls c hc
    have hai := ((mem_cls ha).mp hi).2
    rw [mem_cls ha]
    constructor
    · intro h; exact ⟨hj, mr_trans hai h⟩
    · intro h; exact mr_trans (mr_symm hai) h.2
  · intro a b ha hb hab ⟨i, hi, j, hj, hr⟩
    obtain ⟨a', ha', hca⟩ := hcls cs[a] (List.getElem_mem ha)
    obtain ⟨b', hb', hcb⟩ := hcls cs[b] (List.getElem_mem hb)
    have hjn : j < n := by rw [hcb] at hj; exact cls_lt hb' hj
    have hrd := readyList_get [] cs hrl a ha
    simp only [List.nil_append] at hrd
    unfold ready at hrd
    have h1 := (List.all_eq_true.mp hrd) i hi
    have h2 := (List.all_eq_true.mp h1) j (List.mem_range.mpr hjn)
    simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
      List.any_eq_true] at h2
    have hpw := List.pairwise_iff_getElem.mp hdisj
    rcases h2 with hja | ⟨p, hp', hjp⟩
    · exfalso
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · exact hpw a b ha hb h j hja hj
      · exact hpw b a hb ha h j hj hja
    · obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hp'
      have hkb : k = b := by
        apply Classical.byContradiction
        intro hne
        have hk' : k < cs.length := (Nat.lt_min.mp hk).2
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact hpw k b hk' hb h j hjp hj
        · exact hpw b k hb hk' h j hj hjp
      subst hkb
      exact (Nat.lt_min.mp hk).1

end StandardElm.Src.Grouping
