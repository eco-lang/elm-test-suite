/-
  A Standard Definition of Elm? Mechanisation: objects are unordered (ruling A76), plan step 4.

  `BVal.mkObj` keeps, of the bindings of one key, the last (`dedupLastByKey`), and sorts by key by
  insertion (`insertByKey`). Sorting gives a permutation sorted by key, and two permutations of one
  key-unique list both sorted by key are equal (`List.Perm.eq_of_pairwise`), so the order of the
  bindings does not matter (`a76_mkObj_perm`). A lookup in `mkObj kvs` finds the last binding of
  the key in kvs, so a key outside a record type does not change its decoding
  (`a76_dec_extra_key`).
-/
import StandardElmMech.Eff.Properties

namespace StandardElm.Eff
open StandardElm

abbrev Bind := String × BVal

/-- Sorted by key (non-strictly). -/
def KeyLe (a b : Bind) : Prop := a.1 ≤ b.1

def keysOf (l : List Bind) : List String := l.map (·.1)

/-! ## Sorting by insertion -/

theorem insertByKey_perm (b : Bind) : ∀ l : List Bind, (insertByKey b l).Perm (b :: l)
  | [] => by simp [insertByKey]
  | c :: rest => by
    unfold insertByKey
    split
    · exact List.Perm.refl _
    · exact ((insertByKey_perm b rest).cons c).trans (List.Perm.swap b c rest)

theorem insertByKey_sorted (b : Bind) : ∀ l : List Bind, l.Pairwise KeyLe →
    (insertByKey b l).Pairwise KeyLe
  | [], _ => by simp [insertByKey]
  | c :: rest, h => by
    unfold insertByKey
    rw [List.pairwise_cons] at h
    split
    · rename_i hbc
      have hbc : b.1 ≤ c.1 := of_decide_eq_true hbc
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr h⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hbc
      · exact String.le_trans hbc (h.1 x hx)
    · rename_i hbc
      have hcb : c.1 ≤ b.1 := by
        rcases String.le_total b.1 c.1 with h' | h'
        · exact absurd (decide_eq_true h') hbc
        · exact h'
      refine List.pairwise_cons.mpr ⟨?_, insertByKey_sorted b rest h.2⟩
      intro x hx
      rcases List.mem_cons.mp ((insertByKey_perm b rest).mem_iff.mp hx) with rfl | hx
      · exact hcb
      · exact h.1 x hx

def sortByKey (l : List Bind) : List Bind := l.foldr insertByKey []

theorem sortByKey_perm : ∀ l : List Bind, (sortByKey l).Perm l
  | [] => List.Perm.refl _
  | b :: l => (insertByKey_perm b _).trans ((sortByKey_perm l).cons b)

theorem sortByKey_sorted : ∀ l : List Bind, (sortByKey l).Pairwise KeyLe
  | [] => List.Pairwise.nil
  | b :: l => insertByKey_sorted b _ (sortByKey_sorted l)

/-! ## Keeping the last binding of each key -/

theorem mem_of_keys_nodup_eq : ∀ {l : List Bind} {a b : Bind}, (keysOf l).Nodup → a ∈ l → b ∈ l →
    a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: rest, a, b, hn, ha, hb, he => by
    simp only [keysOf, List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    have notin : ∀ x ∈ rest, x.1 ≠ c.1 := fun x hx hx' => hn.1 (hx' ▸ List.mem_map_of_mem hx)
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd he.symm (notin b hb)
    · exact absurd he (notin a ha)
    · exact mem_of_keys_nodup_eq hn.2 ha hb he

theorem dedup_step_nodup (acc : List Bind) (k : String) (j : BVal) (h : k ∉ keysOf acc) :
    acc.filter (·.1 != k) ++ [(k, j)] = acc ++ [(k, j)] := by
  congr 1
  apply List.filter_eq_self.mpr
  intro x hx
  have : x.1 ≠ k := fun he => h (he ▸ List.mem_map_of_mem hx)
  simpa using this

theorem dedup_foldl_nodup : ∀ (l acc : List Bind), (keysOf (acc ++ l)).Nodup →
    l.foldl (fun acc (k, j) => acc.filter (·.1 != k) ++ [(k, j)]) acc = acc ++ l
  | [], acc, _ => by simp
  | (k, j) :: l, acc, h => by
    simp only [List.foldl_cons]
    have hk : k ∉ keysOf acc := by
      intro hm
      simp only [keysOf, List.map_append, List.map_cons] at h hm
      exact (List.nodup_append.mp h).2.2 k hm k (List.mem_cons_self) rfl
    rw [dedup_step_nodup acc k j hk, dedup_foldl_nodup l (acc ++ [(k, j)]) (by simpa using h)]
    simp

theorem dedupLastByKey_nodup (l : List Bind) (h : (keysOf l).Nodup) : dedupLastByKey l = l := by
  unfold dedupLastByKey
  exact dedup_foldl_nodup l [] (by simpa using h)

/-- A76: objects are unordered: the order of an object's distinct keys does not matter. -/
theorem a76_mkObj_perm {kvs kvs' : List Bind} (hp : kvs.Perm kvs') (hn : (kvs.map (·.1)).Nodup) :
    BVal.mkObj kvs = BVal.mkObj kvs' := by
  have hn' : (keysOf kvs').Nodup := by unfold keysOf; exact (hp.map Prod.fst).nodup_iff.mp hn
  unfold BVal.mkObj
  rw [dedupLastByKey_nodup kvs hn, dedupLastByKey_nodup kvs' hn']
  congr 1
  apply List.Perm.eq_of_pairwise _ (sortByKey_sorted kvs) (sortByKey_sorted kvs')
  · exact ((sortByKey_perm kvs).trans hp).trans (sortByKey_perm kvs').symm
  · intro a b ha hb hab hba
    have ha' : a ∈ kvs := (sortByKey_perm kvs).mem_iff.mp ha
    have hb' : b ∈ kvs := hp.mem_iff.mpr ((sortByKey_perm kvs').mem_iff.mp hb)
    exact mem_of_keys_nodup_eq hn ha' hb' (String.le_antisymm hab hba)

/-! ## Lookups through `mkObj` -/

theorem lookup_ofList (k : String) : ∀ l : List Bind, (BObj.ofList l).lookup k = fmLookup l k
  | [] => rfl
  | (k', j) :: l => by simp [BObj.ofList, BObj.lookup, fmLookup, lookup_ofList k l]

theorem fmLookup_append' (k : String) : ∀ (l1 l2 : List Bind),
    fmLookup (l1 ++ l2) k = match fmLookup l1 k with
      | some v => some v
      | none => fmLookup l2 k
  | [], l2 => rfl
  | (a, v) :: l1, l2 => by
    simp only [List.cons_append, fmLookup]
    split
    · rfl
    · exact fmLookup_append' k l1 l2

/-- The value of the last binding of k. -/
def lookupLast (l : List Bind) (k : String) : Option BVal := fmLookup l.reverse k

theorem fmLookup_filter_ne (l : List Bind) (k k' : String) (h : k' ≠ k) :
    fmLookup (l.filter (·.1 != k')) k = fmLookup l k := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨a, v⟩ := x
    by_cases ha : a = k'
    · subst ha
      have : (a == k) = false := by simpa using h
      simp [fmLookup, this, ih]
    · have : (a != k') = true := by simpa using ha
      simp only [List.filter_cons, this, ite_true, fmLookup]
      rw [ih]

theorem fmLookup_append_single (acc : List Bind) (k k' : String) (j : BVal) :
    fmLookup (acc.filter (·.1 != k') ++ [(k', j)]) k = if k' = k then some j else fmLookup acc k := by
  induction acc with
  | nil => by_cases h : k' = k <;> simp [fmLookup, h]
  | cons x rest ih =>
    obtain ⟨a, v⟩ := x
    by_cases ha : a = k'
    · subst ha; simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rw [ih]
      by_cases h : a = k <;> simp [fmLookup, h]
    · have : (a != k') = true := by simpa using ha
      simp only [List.filter_cons, this, ite_true, List.cons_append, fmLookup]
      rw [ih]
      by_cases h1 : a = k
      · subst h1; simp [Ne.symm ha]
      · have : (a == k) = false := by simpa using h1
        simp [this]

theorem dedup_foldl_lookup (k : String) : ∀ (l acc : List Bind),
    fmLookup (l.foldl (fun acc (k, j) => acc.filter (·.1 != k) ++ [(k, j)]) acc) k =
      match lookupLast l k with
      | some j => some j
      | none => fmLookup acc k
  | [], acc => by simp [lookupLast, fmLookup]
  | (k', j) :: l, acc => by
    simp only [List.foldl_cons]
    rw [dedup_foldl_lookup k l]
    have hl : lookupLast ((k', j) :: l) k =
        match lookupLast l k with
        | some x => some x
        | none => if k' = k then some j else none := by
      unfold lookupLast
      rw [List.reverse_cons, fmLookup_append']
      cases fmLookup l.reverse k <;> by_cases h : k' = k <;> simp [fmLookup, h]
    rw [hl]
    cases lookupLast l k with
    | some x => rfl
    | none =>
      simp only
      rw [fmLookup_append_single]
      by_cases h : k' = k <;> simp [h]

theorem dedup_keys_nodup : ∀ (l acc : List Bind), (keysOf acc).Nodup →
    (keysOf (l.foldl (fun acc (k, j) => acc.filter (·.1 != k) ++ [(k, j)]) acc)).Nodup
  | [], _, h => h
  | (k, j) :: l, acc, h => by
    simp only [List.foldl_cons]
    apply dedup_keys_nodup l
    simp only [keysOf, List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · exact (h.sublist (List.Sublist.map _ (List.filter_sublist)))
    · intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := (List.mem_filter.mp hx).2
      simp at this

theorem lookup_insertByKey (k : String) (b : Bind) : ∀ m : List Bind, b.1 ∉ keysOf m →
    fmLookup (insertByKey b m) k = if b.1 = k then some b.2 else fmLookup m k
  | [], _ => by obtain ⟨a, v⟩ := b; by_cases h : a = k <;> simp [insertByKey, fmLookup, h]
  | c :: rest, hn => by
    obtain ⟨a, v⟩ := b
    obtain ⟨c1, c2⟩ := c
    simp only [keysOf, List.map_cons, List.mem_cons, not_or] at hn
    unfold insertByKey
    split
    · by_cases h : a = k <;> simp [fmLookup, h]
    · simp only [fmLookup]
      rw [lookup_insertByKey k (a, v) rest hn.2]
      by_cases hc : c1 = k
      · subst hc
        have : a ≠ c1 := hn.1
        simp [this]
      · have : (c1 == k) = false := by simpa using hc
        simp [this]

theorem keysOf_sortByKey_perm (l : List Bind) : (keysOf (sortByKey l)).Perm (keysOf l) :=
  (sortByKey_perm l).map _

theorem lookup_sortByKey (k : String) : ∀ l : List Bind, (keysOf l).Nodup →
    fmLookup (sortByKey l) k = fmLookup l k
  | [], _ => rfl
  | (a, v) :: l, hn => by
    simp only [keysOf, List.map_cons, List.nodup_cons] at hn
    show fmLookup (insertByKey (a, v) (sortByKey l)) k = _
    rw [lookup_insertByKey k (a, v) _ (fun hm => hn.1 ((keysOf_sortByKey_perm l).mem_iff.mp hm)),
      lookup_sortByKey k l hn.2]
    by_cases h : a = k <;> simp [fmLookup, h]

/-- A lookup in `mkObj kvs` finds the last binding of the key in kvs. -/
theorem lookup_mkObj (kvs : List Bind) (k : String) :
    (match BVal.mkObj kvs with | .obj o => o.lookup k | _ => none) = lookupLast kvs k := by
  unfold BVal.mkObj BVal.object
  simp only
  rw [lookup_ofList]
  show fmLookup (sortByKey (dedupLastByKey kvs)) k = _
  rw [lookup_sortByKey k _ (by unfold dedupLastByKey; exact dedup_keys_nodup _ [] List.nodup_nil)]
  unfold dedupLastByKey
  rw [dedup_foldl_lookup]
  cases lookupLast kvs k <;> rfl

theorem decFields_congr : ∀ (fs : PFields) (o o' : BObj), (∀ l ∈ fs.labels, o.lookup l = o'.lookup l) →
    decFields fs o = decFields fs o'
  | .nil, _, _, _ => by simp [decFields]
  | .cons l τ rest, o, o', h => by
    simp only [decFields]
    rw [h l (by simp [PFields.labels]),
      decFields_congr rest o o' (fun l' hl' => h l' (by simp [PFields.labels, hl']))]

/-- A76: decoding ignores further keys: adding a key absent from the record type leaves the result
    unchanged. -/
theorem a76_dec_extra_key {fs : PFields} {l : String} {j : BVal} {kvs : List Bind}
    (hl : l ∉ fs.labels) :
    dec (.record fs) (BVal.mkObj ((l, j) :: kvs)) = dec (.record fs) (BVal.mkObj kvs) := by
  have hobj : ∀ kvs : List Bind, ∃ o, BVal.mkObj kvs = .obj o := fun kvs => ⟨_, rfl⟩
  obtain ⟨o1, h1⟩ := hobj ((l, j) :: kvs)
  obtain ⟨o2, h2⟩ := hobj kvs
  have e1 := lookup_mkObj ((l, j) :: kvs)
  have e2 := lookup_mkObj kvs
  rw [h1] at e1 ⊢
  rw [h2] at e2 ⊢
  simp only at e1 e2
  simp only [dec]
  rw [decFields_congr fs o1 o2]
  intro k hk
  have hkl : l ≠ k := fun he => hl (he ▸ hk)
  rw [e1, e2]
  unfold lookupLast
  rw [List.reverse_cons, fmLookup_append']
  cases fmLookup kvs.reverse k <;> simp [fmLookup, hkl]

end StandardElm.Eff
