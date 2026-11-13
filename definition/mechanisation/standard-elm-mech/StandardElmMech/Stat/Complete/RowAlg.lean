/-
  A Standard Definition of Elm? Mechanisation: rows as sorted lists, milestone (d) of plan step 11
  (section 1: a row is a finite map from labels to types; section 4, K8).

  Step 9 represents a row by a list of fields; the canonical representation of a finite map is the
  list *strictly sorted* by `labLt` (Objects.lean: `rowSorted`, `Row.insert`, `Row.merge`), and two
  canonical rows are equal as maps iff they are equal as lists (`sorted_ext`). Substituting a row
  variable merges two rows; here the merge is the *total* merge `mrg` of two lists by label (the
  left field first on equal labels), so that substitution is a total function whose algebra holds
  unconditionally: `mrg` commutes with a map on the field types (`mrg_mapV`) and is associative
  (`mrg_assoc`), for all lists. On sorted rows with disjoint labels it is the union (sorted:
  `sorted_mrg`), and a merge is sorted only if its two arguments are sorted and have disjoint
  labels (`sorted_of_mrg`): a substitution that would give a record a label twice gives a row that
  is not sorted (A23).
-/
import StandardElmMech.Stat.Complete.FSubst

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-! ## The order of labels: a strict total order -/

theorem char_tri (a b : Char) : a.val < b.val ∨ a = b ∨ b.val < a.val := by
  rcases Nat.lt_trichotomy a.val.toNat b.val.toNat with h | h | h
  · exact .inl (UInt32.lt_iff_toNat_lt.mpr h)
  · exact .inr (.inl (Char.ext (UInt32.toNat_inj.mp h)))
  · exact .inr (.inr (UInt32.lt_iff_toNat_lt.mpr h))

theorem char_lt_irrefl (a : Char) : ¬ a.val < a.val := by
  rw [UInt32.lt_iff_toNat_lt]; exact Nat.lt_irrefl _

theorem char_lt_trans {a b c : Char} (h1 : a.val < b.val) (h2 : b.val < c.val) : a.val < c.val := by
  rw [UInt32.lt_iff_toNat_lt] at *; omega

theorem char_lt_asymm {a b : Char} (h1 : a.val < b.val) : ¬ b.val < a.val := by
  rw [UInt32.lt_iff_toNat_lt] at *; omega

theorem charsLt_irrefl : ∀ l : List Char, charsLt l l = false
  | [] => rfl
  | a :: as => by simp [charsLt, char_lt_irrefl, charsLt_irrefl as]

theorem charsLt_cons {a b : Char} {as bs : List Char} :
    charsLt (a :: as) (b :: bs) = true ↔ a.val < b.val ∨ (a = b ∧ charsLt as bs = true) := by
  simp only [charsLt]
  by_cases h : a.val < b.val
  · simp [h]
  · by_cases h' : a = b
    · subst h'; simp [h]
    · simp [h, h']

theorem charsLt_trans : ∀ a b c : List Char, charsLt a b = true → charsLt b c = true → charsLt a c = true
  | [], [], _, h, _ => by simp [charsLt] at h
  | [], _ :: _, [], _, h => by simp [charsLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [charsLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [charsLt] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    rw [charsLt_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact .inl (char_lt_trans h1 h2)
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, charsLt_trans as bs cs h1 h2⟩

theorem charsLt_tri : ∀ a b : List Char, charsLt a b = true ∨ a = b ∨ charsLt b a = true
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inl rfl
  | _ :: _, [] => .inr (.inr rfl)
  | a :: as, b :: bs => by
    rw [charsLt_cons, charsLt_cons]
    rcases char_tri a b with h | rfl | h
    · exact .inl (.inl h)
    · rcases charsLt_tri as bs with h | rfl | h
      · exact .inl (.inr ⟨rfl, h⟩)
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr ⟨rfl, h⟩))
    · exact .inr (.inr (.inl h))

theorem labLt_irrefl (a : Lab) : labLt a a = false := charsLt_irrefl _

theorem labLt_trans {a b c : Lab} (h1 : labLt a b = true) (h2 : labLt b c = true) : labLt a c = true :=
  charsLt_trans _ _ _ h1 h2

theorem labLt_tri (a b : Lab) : labLt a b = true ∨ a = b ∨ labLt b a = true := by
  rcases charsLt_tri a.toList b.toList with h | h | h
  · exact .inl h
  · exact .inr (.inl (String.ext h))
  · exact .inr (.inr h)

theorem labLt_asymm {a b : Lab} (h : labLt a b = true) : labLt b a = false := by
  cases e : labLt b a
  · rfl
  · have := labLt_trans h e; rw [labLt_irrefl] at this; cases this

theorem labLt_ne {a b : Lab} (h : labLt a b = true) : a ≠ b := by
  rintro rfl; rw [labLt_irrefl] at h; cases h

/-! ## The merge -/

/-- A field goes before another: by label, the left one first on equal labels. -/
def fLe (p q : Lab × Ty) : Bool := !labLt q.1 p.1

/-- The merge of `p :: r1` (with `m` the merge of `r1`) into a list, by recursion on that list. -/
def mrgAux (p : Lab × Ty) (r1 : Row) (m : Row → Row) : Row → Row
  | [] => p :: r1
  | q :: r2 => if fLe p q then p :: m (q :: r2) else q :: mrgAux p r1 m r2

/-- The merge of two rows by label, the left fields first on equal labels. Total and structural. -/
def mrg : Row → Row → Row
  | [], r2 => r2
  | p :: r1, r2 => mrgAux p r1 (mrg r1) r2

theorem mrg_nil_left (r : Row) : mrg [] r = r := rfl

theorem mrg_nil_right : ∀ r : Row, mrg r [] = r
  | [] => rfl
  | _ :: _ => rfl

theorem mrg_cons_nil (p : Lab × Ty) (r : Row) : mrg (p :: r) [] = p :: r := rfl

theorem mrg_cons_cons (p q : Lab × Ty) (r1 r2 : Row) :
    mrg (p :: r1) (q :: r2) = if fLe p q then p :: mrg r1 (q :: r2) else q :: mrg (p :: r1) r2 := rfl

/-- The fields of a row with their types mapped. -/
def mapV (f : Ty → Ty) (r : Row) : Row := r.map fun p => (p.1, f p.2)

theorem mapV_nil (f : Ty → Ty) : mapV f [] = [] := rfl
theorem mapV_cons (f : Ty → Ty) (p : Lab × Ty) (r : Row) : mapV f (p :: r) = (p.1, f p.2) :: mapV f r := rfl

theorem fLe_iff {p q : Lab × Ty} : fLe p q = true ↔ labLt q.1 p.1 = false := by
  simp [fLe]

theorem not_fLe {p q : Lab × Ty} : ¬ fLe p q = true ↔ labLt q.1 p.1 = true := by
  simp [fLe]

theorem mrg_mapV (f : Ty → Ty) : ∀ a b : Row, mrg (mapV f a) (mapV f b) = mapV f (mrg a b)
  | [], b => rfl
  | p :: a, b => by
    induction b with
    | nil => rfl
    | cons q b ih =>
      rw [mapV_cons, mapV_cons, mrg_cons_cons, mrg_cons_cons]
      have e : fLe (p.1, f p.2) (q.1, f q.2) = fLe p q := rfl
      rw [e]
      by_cases h : fLe p q = true
      · rw [if_pos h, if_pos h, ← mapV_cons, mrg_mapV f a (q :: b)]; rfl
      · rw [if_neg h, if_neg h, ← mapV_cons, ih]; rfl

theorem mrg_assoc : ∀ a b c : Row, mrg (mrg a b) c = mrg a (mrg b c)
  | [], b, c => rfl
  | a, [], c => by rw [mrg_nil_right]; rfl
  | a, b, [] => by rw [mrg_nil_right, mrg_nil_right]
  | x :: a, y :: b, z :: c => by
    rw [mrg_cons_cons x y]
    by_cases hxy : fLe x y = true
    · rw [if_pos hxy, mrg_cons_cons x z]
      rw [mrg_cons_cons y z]
      by_cases hyz : fLe y z = true
      · have hxz : fLe x z = true := by
          rw [fLe_iff] at hxy hyz ⊢
          rcases labLt_tri z.1 x.1 with h | h | h
          · rcases labLt_tri y.1 x.1 with h' | h' | h'
            · rw [h'] at hxy; cases hxy
            · rw [← h'] at h; rw [h] at hyz; cases hyz
            · rw [labLt_trans h h'] at hyz; cases hyz
          · rw [h, labLt_irrefl]
          · exact labLt_asymm h
        rw [if_pos hxz, if_pos hyz, mrg_cons_cons x y, if_pos hxy, mrg_assoc a (y :: b) (z :: c),
          mrg_cons_cons y z, if_pos hyz]
      · rw [if_neg hyz, mrg_cons_cons x z]
        by_cases hxz : fLe x z = true
        · rw [if_pos hxz, if_pos hxz, mrg_assoc a (y :: b) (z :: c), mrg_cons_cons y z, if_neg hyz]
        · rw [if_neg hxz, if_neg hxz, ← mrg_assoc (x :: a) (y :: b) c, mrg_cons_cons x y, if_pos hxy]
    · rw [if_neg hxy]
      rw [mrg_cons_cons y z]
      by_cases hyz : fLe y z = true
      · rw [if_pos hyz, mrg_cons_cons y z, if_pos hyz, mrg_cons_cons x y, if_neg hxy,
          mrg_assoc (x :: a) b (z :: c)]
      · have hxz : fLe x z = false := by
          rw [not_fLe] at hxy hyz
          simp only [fLe, labLt_trans hyz hxy, Bool.not_true]
        rw [if_neg hyz, mrg_cons_cons y z, if_neg hyz, mrg_cons_cons x z, hxz]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← mrg_assoc (x :: a) (y :: b) c, mrg_cons_cons x y, if_neg hxy]
termination_by a b c => a.length + b.length + c.length

theorem mrg_perm : ∀ a b : Row, (mrg a b).Perm (a ++ b)
  | [], b => List.Perm.refl _
  | p :: a, b => by
    induction b with
    | nil => rw [mrg_cons_nil, List.append_nil]
    | cons q b ih =>
      rw [mrg_cons_cons]
      split
      · exact (mrg_perm a (q :: b)).cons p
      · exact (ih.cons q).trans (List.perm_middle.symm)

theorem mem_mrg {x : Lab × Ty} {a b : Row} : x ∈ mrg a b ↔ x ∈ a ∨ x ∈ b := by
  rw [(mrg_perm a b).mem_iff, List.mem_append]

theorem sublist_mrg_left : ∀ a b : Row, a.Sublist (mrg a b)
  | [], _ => List.nil_sublist _
  | p :: a, b => by
    induction b with
    | nil => exact List.Sublist.refl _
    | cons q b ih =>
      rw [mrg_cons_cons]
      split
      · exact (sublist_mrg_left a (q :: b)).cons_cons p
      · exact ih.cons q

theorem sublist_mrg_right : ∀ a b : Row, b.Sublist (mrg a b)
  | [], _ => List.Sublist.refl _
  | p :: a, b => by
    induction b with
    | nil => exact List.nil_sublist _
    | cons q b ih =>
      rw [mrg_cons_cons]
      split
      · exact (sublist_mrg_right a (q :: b)).cons p
      · exact ih.cons_cons q

theorem mrg_length (a b : Row) : (mrg a b).length = a.length + b.length := by
  rw [(mrg_perm a b).length_eq, List.length_append]

theorem rsize_append : ∀ a b : Row, rsize (a ++ b) = rsize a + rsize b
  | [], b => by simp [rsize]
  | (l, τ) :: a, b => by simp only [List.cons_append, rsize, rsize_append a b]; omega

theorem rsize_mrg : ∀ a b : Row, rsize (mrg a b) = rsize a + rsize b
  | [], b => by simp [mrg, rsize]
  | p :: a, b => by
    induction b with
    | nil => rw [mrg_cons_nil]; simp [rsize]
    | cons q b ih =>
      rw [mrg_cons_cons]
      obtain ⟨l, τ⟩ := p
      obtain ⟨l', τ'⟩ := q
      split
      · simp only [rsize]; rw [rsize_mrg a ((l', τ') :: b)]; simp only [rsize]; omega
      · simp only [rsize] at ih ⊢; rw [ih]; omega

theorem mrg_eq_nil {a b : Row} (h : mrg a b = []) : a = [] ∧ b = [] := by
  have := mrg_length a b; rw [h] at this
  exact ⟨List.length_eq_zero_iff.mp (by simp at this; omega), List.length_eq_zero_iff.mp (by simp at this; omega)⟩

/-! ## Sorted rows -/

/-- The labels of the fields strictly increase. -/
def FLt (p q : Lab × Ty) : Prop := labLt p.1 q.1 = true

/-- A canonical row: strictly sorted by label. -/
def Sorted (r : Row) : Prop := r.Pairwise FLt

theorem sorted_nil : Sorted [] := List.Pairwise.nil

theorem sorted_labels_ne {r : Row} (h : Sorted r) : r.Pairwise fun p q => p.1 ≠ q.1 :=
  h.imp fun h => labLt_ne h

/-- In a sorted row a label determines the field. -/
theorem sorted_unique {r : Row} (h : Sorted r) {x y : Lab × Ty} (hx : x ∈ r) (hy : y ∈ r) (hl : x.1 = y.1) :
    x = y := by
  induction r with
  | nil => cases hx
  | cons p r ih =>
    rw [Sorted, List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · rw [ex, ey]
    · have := h.1 y hy'; rw [FLt, ← ex, ← hl, labLt_irrefl] at this; cases this
    · have := h.1 x hx'; rw [FLt, ← ey, hl, labLt_irrefl] at this; cases this
    · exact ih h.2 hx' hy'

/-- Two sorted rows with the same fields are equal. -/
theorem sorted_ext : ∀ {a b : Row}, Sorted a → Sorted b → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).mpr (List.mem_cons_self ..)) (by simp)
  | x :: _, [], _, _, h => absurd ((h x).mp (List.mem_cons_self ..)) (by simp)
  | x :: a, y :: b, ha, hb, h => by
    have ha' := ha; have hb' := hb
    rw [Sorted, List.pairwise_cons] at ha' hb'
    have hxy : x = y := by
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_self ..)) with e | hx
      · exact e
      rcases List.mem_cons.mp ((h y).mpr (List.mem_cons_self ..)) with e | hy
      · exact e.symm
      have h1 := hb'.1 x hx; have h2 := ha'.1 y hy
      unfold FLt at h1 h2; rw [labLt_asymm h1] at h2; cases h2
    subst hxy
    have hxa : x ∉ a := fun hm => by have := ha'.1 x hm; rw [FLt, labLt_irrefl] at this; cases this
    have hxb : x ∉ b := fun hm => by have := hb'.1 x hm; rw [FLt, labLt_irrefl] at this; cases this
    rw [sorted_ext ha'.2 hb'.2 fun z => ?_]
    constructor
    · intro hz
      rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd hz hxa
      · exact e
    · intro hz
      rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd hz hxb
      · exact e

/-- Labels disjoint. -/
def LDisj (a b : Row) : Prop := ∀ x ∈ a, ∀ y ∈ b, x.1 ≠ y.1

theorem sorted_mrg : ∀ {a b : Row}, Sorted a → Sorted b → LDisj a b → Sorted (mrg a b)
  | [], _, _, hb, _ => hb
  | p :: a, b, ha, hb, hd => by
    induction b with
    | nil => exact ha
    | cons q b ih =>
      have ha' := ha; have hb' := hb
      rw [Sorted, List.pairwise_cons] at ha' hb'
      rw [mrg_cons_cons]
      split
      · rename_i hle
        have hpq : labLt p.1 q.1 = true := by
          simp only [fLe, Bool.not_eq_true'] at hle
          rcases labLt_tri p.1 q.1 with h | h | h
          · exact h
          · exact absurd h (hd p (List.mem_cons_self ..) q (List.mem_cons_self ..))
          · rw [h] at hle; cases hle
        refine List.Pairwise.cons (fun z hz => ?_) (sorted_mrg ha'.2 hb fun x hx y hy => hd x (List.mem_cons_of_mem _ hx) y hy)
        rcases mem_mrg.mp hz with hz | hz
        · exact ha'.1 z hz
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact hpq
          · exact labLt_trans hpq (hb'.1 z hz)
      · rename_i hle
        have hqp : labLt q.1 p.1 = true := by simpa [fLe] using hle
        refine List.Pairwise.cons (fun z hz => ?_) (ih hb'.2 fun x hx y hy => hd x hx y (List.mem_cons_of_mem _ hy))
        rcases mem_mrg.mp hz with hz | hz
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact hqp
          · exact labLt_trans hqp (ha'.1 z hz)
        · exact hb'.1 z hz

theorem sorted_of_mrg {a b : Row} (h : Sorted (mrg a b)) : Sorted a ∧ Sorted b ∧ LDisj a b := by
  refine ⟨h.sublist (sublist_mrg_left a b), h.sublist (sublist_mrg_right a b), ?_⟩
  have h1 := sorted_labels_ne h
  rw [List.Perm.pairwise_iff (fun h => Ne.symm h) (mrg_perm a b), List.pairwise_append] at h1
  exact h1.2.2

theorem sorted_cons {p : Lab × Ty} {r : Row} : Sorted (p :: r) ↔ (∀ q ∈ r, FLt p q) ∧ Sorted r :=
  List.pairwise_cons

theorem sorted_filter {r : Row} (f : Lab × Ty → Bool) (h : Sorted r) : Sorted (r.filter f) :=
  h.sublist List.filter_sublist

theorem sorted_mapV_iff (f : Ty → Ty) {r : Row} : Sorted (mapV f r) ↔ Sorted r := by
  unfold Sorted mapV
  rw [List.pairwise_map]
  rfl

theorem mem_mapV {f : Ty → Ty} {r : Row} {x : Lab × Ty} : x ∈ mapV f r ↔ ∃ p ∈ r, x = (p.1, f p.2) := by
  unfold mapV; simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

theorem ldisj_mapV_iff (f g : Ty → Ty) {a b : Row} : LDisj (mapV f a) (mapV g b) ↔ LDisj a b := by
  constructor
  · intro h x hx y hy
    exact h (x.1, f x.2) (mem_mapV.mpr ⟨x, hx, rfl⟩) (y.1, g y.2) (mem_mapV.mpr ⟨y, hy, rfl⟩)
  · intro h x hx y hy
    obtain ⟨p, hp, rfl⟩ := mem_mapV.mp hx
    obtain ⟨q, hq, rfl⟩ := mem_mapV.mp hy
    exact h p hp q hq

theorem ldisj_comm {a b : Row} (h : LDisj a b) : LDisj b a := fun x hx y hy e => h y hy x hx e.symm

theorem ldisj_nil_right (a : Row) : LDisj a [] := fun _ _ _ hy => nomatch hy

theorem ldisj_mrg_right {a b c : Row} : LDisj a (mrg b c) ↔ LDisj a b ∧ LDisj a c := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (mem_mrg.mpr (.inl hy)), fun x hx y hy => h x hx y (mem_mrg.mpr (.inr hy))⟩
  · rintro ⟨h1, h2⟩ x hx y hy
    rcases mem_mrg.mp hy with hy | hy
    · exact h1 x hx y hy
    · exact h2 x hx y hy

theorem ldisj_mrg_left {a b c : Row} : LDisj (mrg b c) a ↔ LDisj b a ∧ LDisj c a := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x (mem_mrg.mpr (.inl hx)) y hy, fun x hx y hy => h x (mem_mrg.mpr (.inr hx)) y hy⟩
  · rintro ⟨h1, h2⟩ x hx y hy
    rcases mem_mrg.mp hx with hx | hx
    · exact h1 x hx y hy
    · exact h2 x hx y hy

/-- The labels of a row. -/

theorem mem_labs {l : Lab} {r : Row} : l ∈ labs r ↔ ∃ τ, (l, τ) ∈ r := by
  unfold labs; simp only [List.mem_map]
  constructor
  · rintro ⟨⟨l', τ⟩, h, rfl⟩; exact ⟨τ, h⟩
  · rintro ⟨τ, h⟩; exact ⟨(l, τ), h, rfl⟩

theorem labs_mapV (f : Ty → Ty) (r : Row) : labs (mapV f r) = labs r := by
  unfold labs mapV; simp

/-- `rowSorted` (Objects.lean) is `Sorted`. -/
theorem rowSorted_iff : ∀ r : Row, rowSorted (labs r) = true ↔ Sorted r
  | [] => by simp [rowSorted, labs, Sorted]
  | [p] => by simp [rowSorted, labs, Sorted]
  | p :: q :: r => by
    have ih := rowSorted_iff (q :: r)
    have e : rowSorted (labs (p :: q :: r)) = (labLt p.1 q.1 && rowSorted (labs (q :: r))) := rfl
    rw [e, Bool.and_eq_true, ih, sorted_cons (p := p) (r := q :: r)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun z hz => ?_, h2⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h1
      · exact labLt_trans h1 ((sorted_cons.mp h2).1 z hz)
    · rintro ⟨h1, h2⟩
      exact ⟨h1 q (List.mem_cons_self ..), h2⟩

end StandardElm.Stat.Complete
