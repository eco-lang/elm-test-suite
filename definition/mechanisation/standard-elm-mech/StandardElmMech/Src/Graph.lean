/-
  A Standard Definition of Elm? Mechanisation: reachability on graphs over 0 .. n-1, plan step 8
  (section 4). `Plus n r i j`: one or more steps of `r`; `plusB` decides it, by growing the set of
  targets reached from `i` until it no longer grows (at most n times); `plusB_iff` proves it
  correct. The stabilisation argument counts members of filters of `List.range n`: a set that does
  not grow is closed under `r`, and a set that grows n times has n members, all of them.
-/

namespace StandardElm.Src.Graph

/-- One or more steps of `r` among `0 .. n-1`. -/
inductive Plus (n : Nat) (r : Nat → Nat → Bool) : Nat → Nat → Prop where
  | step {i j : Nat} : i < n → j < n → r i j = true → Plus n r i j
  | trans {i j k : Nat} : Plus n r i j → Plus n r j k → Plus n r i k

/-- Zero or more steps. -/
def Reach (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Prop := i = j ∨ Plus n r i j

theorem Plus.lt {n : Nat} {r : Nat → Nat → Bool} {i j : Nat} (h : Plus n r i j) : i < n ∧ j < n := by
  induction h with
  | step hi hj _ => exact ⟨hi, hj⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

/-- The first step of a path. -/
theorem Plus.first {n : Nat} {r : Nat → Nat → Bool} {i j : Nat} (h : Plus n r i j) :
    ∃ m, m < n ∧ r i m = true ∧ (m = j ∨ Plus n r m j) := by
  induction h with
  | step _ hj hr => exact ⟨_, hj, hr, .inl rfl⟩
  | trans _ h2 ih1 _ =>
    obtain ⟨m, hm, hr, hj | hp⟩ := ih1
    · subst hj; exact ⟨m, hm, hr, .inr h2⟩
    · exact ⟨m, hm, hr, .inr (.trans hp h2)⟩

/-! ## The decider -/

/-- The targets one step from the set `s`, together with `s`, as a filter of `range n`. -/
def grow (n : Nat) (r : Nat → Nat → Bool) (s : List Nat) : List Nat :=
  (List.range n).filter fun j => s.contains j || s.any fun k => r k j

/-- The targets one step from `i`. -/
def start (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : List Nat :=
  (List.range n).filter fun j => decide (i < n) && r i j

/-- Grow at most `k` times, stopping when the set no longer grows. -/
def iter (n : Nat) (r : Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, s => s
  | k + 1, s => if (grow n r s).length == s.length then s else iter n r k (grow n r s)

def plusSet (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : List Nat := iter n r n (start n r i)

def plusB (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Bool := (plusSet n r i).contains j

def reachB (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Bool := i == j || plusB n r i j

/-! ## Counting the members of filters -/

theorem len_filter_mono {α : Type} : ∀ {l : List α} {p q : α → Bool},
    (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _, _, _ => by simp
  | x :: xs, p, q, h => by
    have ih := len_filter_mono (l := xs) (p := p) (q := q) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem len_filter_eq {α : Type} : ∀ {l : List α} {p q : α → Bool},
    (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length = (l.filter q).length →
    ∀ x ∈ l, q x = true → p x = true
  | [], _, _, _, _, x, hx, _ => by simp at hx
  | y :: ys, p, q, h, he, x, hx, hq => by
    have hle := len_filter_mono (l := ys) (p := p) (q := q) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hy := h y List.mem_cons_self
    simp only [List.filter_cons] at he
    have he' : (ys.filter p).length = (ys.filter q).length := by
      cases hp : p y <;> cases hq' : q y <;> simp_all <;> omega
    rcases List.mem_cons.mp hx with rfl | hx
    · cases hp : p x
      · cases hq' : q x
        · simp_all
        · simp [hp, hq'] at he; omega
      · rfl
    · exact len_filter_eq (fun z hz => h z (List.mem_cons_of_mem _ hz)) he' x hx hq

/-! ## Facts about growing -/

theorem mem_grow {n : Nat} {r : Nat → Nat → Bool} {s : List Nat} {j : Nat} :
    j ∈ grow n r s ↔ j < n ∧ (j ∈ s ∨ ∃ k ∈ s, r k j = true) := by
  simp [grow, List.mem_filter, List.mem_range]

theorem mem_start {n : Nat} {r : Nat → Nat → Bool} {i j : Nat} :
    j ∈ start n r i ↔ j < n ∧ i < n ∧ r i j = true := by
  simp [start, List.mem_filter, List.mem_range]

/-- A set is a filter of `range n`. -/
def Shape (n : Nat) (s : List Nat) : Prop := ∃ q : Nat → Bool, s = (List.range n).filter q

theorem shape_grow (n : Nat) (r : Nat → Nat → Bool) (s : List Nat) : Shape n (grow n r s) := ⟨_, rfl⟩

theorem shape_lt {n : Nat} {s : List Nat} (h : Shape n s) : ∀ j ∈ s, j < n := by
  obtain ⟨q, rfl⟩ := h
  intro j hj
  exact List.mem_range.mp (List.mem_filter.mp hj).1

theorem shape_len {n : Nat} {s : List Nat} (h : Shape n s) : s.length ≤ n := by
  obtain ⟨q, rfl⟩ := h
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- A shaped set is the filter of `range n` by its own membership. -/
theorem shape_self {n : Nat} {s : List Nat} (h : Shape n s) :
    s = (List.range n).filter fun j => s.contains j := by
  obtain ⟨q, rfl⟩ := h
  apply (List.filter_congr _).symm
  intro j hj
  have hj' : j < n := List.mem_range.mp hj
  simp [List.mem_filter, hj']

def Closed (n : Nat) (r : Nat → Nat → Bool) (s : List Nat) : Prop :=
  ∀ a ∈ s, ∀ b, b < n → r a b = true → b ∈ s

theorem grow_ge {n : Nat} {r : Nat → Nat → Bool} {s : List Nat} (hs : Shape n s) : ∀ j ∈ s, j ∈ grow n r s :=
  fun j hj => mem_grow.mpr ⟨shape_lt hs j hj, .inl hj⟩

/-- A shaped set that does not grow is closed. -/
theorem closed_of_len {n : Nat} {r : Nat → Nat → Bool} {s : List Nat} (hs : Shape n s)
    (he : (grow n r s).length = s.length) : Closed n r s := by
  intro a ha b hb hr
  have hself := shape_self hs
  have hmono : ∀ x ∈ List.range n, (fun j => s.contains j) x = true →
      (fun j => s.contains j || s.any fun k => r k j) x = true := by
    intro x _ hx; simp only [Bool.or_eq_true]; exact .inl hx
  have heq : ((List.range n).filter fun j => s.contains j).length =
      ((List.range n).filter fun j => s.contains j || s.any fun k => r k j).length := by
    rw [← hself]; exact he.symm
  have := len_filter_eq hmono heq b (List.mem_range.mpr hb)
    (by simp only [Bool.or_eq_true, List.any_eq_true]; exact .inr ⟨a, ha, hr⟩)
  simpa using this

/-- A shaped set with n members is all of `range n`, so closed. -/
theorem closed_of_full {n : Nat} {r : Nat → Nat → Bool} {s : List Nat} (hs : Shape n s)
    (hl : n ≤ s.length) : Closed n r s := by
  intro a _ b hb _
  have hself := shape_self hs
  have hmono : ∀ x ∈ List.range n, (fun j => s.contains j) x = true → (fun _ => true) x = true :=
    fun _ _ _ => rfl
  have heq : ((List.range n).filter fun j => s.contains j).length = ((List.range n).filter fun _ => true).length := by
    rw [← hself]
    have : ((List.range n).filter fun _ => true) = List.range n := List.filter_eq_self.mpr (by simp)
    rw [this, List.length_range]
    exact Nat.le_antisymm (shape_len hs) hl
  have := len_filter_eq hmono heq b (List.mem_range.mpr hb) rfl
  simpa using this

theorem iter_props (n : Nat) (r : Nat → Nat → Bool) : ∀ (k : Nat) (s : List Nat), Shape n s →
    Shape n (iter n r k s) ∧ (∀ j ∈ s, j ∈ iter n r k s) ∧
      (Closed n r (iter n r k s) ∨ s.length + k ≤ (iter n r k s).length)
  | 0, s, hs => ⟨hs, fun _ h => h, .inr (by simp [iter])⟩
  | k + 1, s, hs => by
    unfold iter
    split
    · rename_i he
      exact ⟨hs, fun _ h => h, .inl (closed_of_len hs (by simpa using he))⟩
    · rename_i hne
      have hge : s.length + 1 ≤ (grow n r s).length := by
        have hm : s.length ≤ (grow n r s).length := by
          have hm' := len_filter_mono (l := List.range n) (p := fun j => s.contains j)
            (q := fun j => s.contains j || s.any fun k => r k j)
            (fun x _ hx => by simp only [Bool.or_eq_true]; exact .inl hx)
          calc s.length = ((List.range n).filter fun j => s.contains j).length := congrArg List.length (shape_self hs)
            _ ≤ _ := hm'
        have : (grow n r s).length ≠ s.length := by simpa using hne
        omega
      obtain ⟨h1, h2, h3⟩ := iter_props n r k (grow n r s) (shape_grow n r s)
      refine ⟨h1, fun j hj => h2 j (grow_ge hs j hj), ?_⟩
      rcases h3 with h | h
      · exact .inl h
      · exact .inr (by omega)

theorem plusSet_closed (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : Closed n r (plusSet n r i) := by
  unfold plusSet
  obtain ⟨hshape, _, h⟩ := iter_props n r n (start n r i) ⟨_, rfl⟩
  rcases h with h | h
  · exact h
  · exact closed_of_full hshape (by omega)

theorem start_sub (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : ∀ j ∈ start n r i, j ∈ plusSet n r i :=
  (iter_props n r n (start n r i) ⟨_, rfl⟩).2.1

theorem iter_sound (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : ∀ (k : Nat) (s : List Nat),
    (∀ j ∈ s, Plus n r i j) → ∀ j ∈ iter n r k s, Plus n r i j
  | 0, _, h => h
  | k + 1, s, h => by
    unfold iter
    split
    · exact h
    · apply iter_sound n r i k
      intro j hj
      obtain ⟨hjn, hj | ⟨m, hm, hr⟩⟩ := mem_grow.mp hj
      · exact h j hj
      · have hp := h m hm
        exact .trans hp (.step hp.lt.2 hjn hr)

theorem reach_closed {n : Nat} {r : Nat → Nat → Bool} {s : List Nat} (hc : Closed n r s) :
    ∀ {a b}, Plus n r a b → a ∈ s → b ∈ s := by
  intro a b h
  induction h with
  | step _ hj hr => exact fun ha => hc _ ha _ hj hr
  | trans _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)

theorem plusB_iff (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : plusB n r i j = true ↔ Plus n r i j := by
  unfold plusB
  rw [List.contains_iff_mem]
  constructor
  · intro h
    exact iter_sound n r i n (start n r i)
      (fun j hj => by obtain ⟨hj, hi, hr⟩ := mem_start.mp hj; exact .step hi hj hr) j h
  · intro h
    obtain ⟨m, hm, hr, hj | hp⟩ := h.first
    · subst hj; exact start_sub n r i m (mem_start.mpr ⟨hm, h.lt.1, hr⟩)
    · exact reach_closed (plusSet_closed n r i) hp (start_sub n r i m (mem_start.mpr ⟨hm, h.lt.1, hr⟩))

instance (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Decidable (Plus n r i j) :=
  decidable_of_iff _ (plusB_iff n r i j)

theorem reachB_iff (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : reachB n r i j = true ↔ Reach n r i j := by
  simp [reachB, Reach, plusB_iff]

instance (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Decidable (Reach n r i j) :=
  decidable_of_iff _ (reachB_iff n r i j)

end StandardElm.Src.Graph
