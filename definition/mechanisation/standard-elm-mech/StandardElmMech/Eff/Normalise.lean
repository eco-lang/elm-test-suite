/-
  A Standard Definition of Elm? Mechanisation: canonical payload types (decision D7), plan step 4.

  `PTy.normalise` sorts the fields of every record type by label (insertion, structural);
  `normalise_canon`: the result is canonical (`PTy.Canon`, the fields of every record strictly
  increasing) when the labels of each record type are distinct (`PTy.distinctB`), as they are in
  every type elaboration accepts. The translator writes payload types already sorted; the generated
  theorems `ports_canon_<Shard>` check, by the kernel, that every port of every translated program
  has a canonical type.
-/
import StandardElmMech.Eff.Properties

namespace StandardElm.Eff
open StandardElm

/-- Insert a field into fields sorted by label. -/
def PFields.insert (l : String) (τ : PTy) : PFields → PFields
  | .nil => .cons l τ .nil
  | .cons l' τ' rest => if l < l' then .cons l τ (.cons l' τ' rest) else .cons l' τ' (PFields.insert l τ rest)

def PFields.sort : PFields → PFields
  | .nil => .nil
  | .cons l τ rest => PFields.insert l τ rest.sort

mutual
  /-- Sort the fields of every record type by label. -/
  def PTy.normalise : PTy → PTy
    | .list τ => .list τ.normalise
    | .maybe τ => .maybe τ.normalise
    | .array τ => .array τ.normalise
    | .tuple2 a b => .tuple2 a.normalise b.normalise
    | .tuple3 a b c => .tuple3 a.normalise b.normalise c.normalise
    | .record fs => .record fs.normaliseEach.sort
    | τ => τ
  /-- Normalise the type of each field. -/
  def PFields.normaliseEach : PFields → PFields
    | .nil => .nil
    | .cons l τ rest => .cons l τ.normalise rest.normaliseEach
end

mutual
  /-- The labels of every record type are distinct. -/
  def PTy.distinctB : PTy → Bool
    | .list τ | .maybe τ | .array τ => τ.distinctB
    | .tuple2 a b => a.distinctB && b.distinctB
    | .tuple3 a b c => a.distinctB && b.distinctB && c.distinctB
    | .record fs => decide fs.labels.Nodup && fs.distinctB
    | _ => true
  def PFields.distinctB : PFields → Bool
    | .nil => true
    | .cons _ τ rest => τ.distinctB && rest.distinctB
end

/-! ## Labels increasing as a pairwise property -/

theorem labelsIncreasing_iff : ∀ fs : PFields, fs.labelsIncreasing = true ↔ fs.labels.Pairwise (· < ·)
  | .nil => by simp [PFields.labelsIncreasing, PFields.labels]
  | .cons l τ .nil => by simp [PFields.labelsIncreasing, PFields.labels]
  | .cons l τ (.cons l' τ' rest) => by
    have ih := labelsIncreasing_iff (.cons l' τ' rest)
    simp only [PFields.labelsIncreasing, Bool.and_eq_true, decide_eq_true_eq, ih]
    simp only [PFields.labels, List.pairwise_cons, List.mem_cons]
    constructor
    · rintro ⟨hll', h1, h2⟩
      refine ⟨?_, h1, h2⟩
      rintro a (rfl | ha)
      · exact hll'
      · exact String.lt_trans hll' (h1 a ha)
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0 l' (.inl rfl), h1, h2⟩

theorem labels_insert_perm (l : String) (τ : PTy) : ∀ fs : PFields,
    (PFields.insert l τ fs).labels.Perm (l :: fs.labels)
  | .nil => by simp [PFields.insert, PFields.labels]
  | .cons l' τ' rest => by
    unfold PFields.insert
    split
    · exact List.Perm.refl _
    · simp only [PFields.labels]
      exact ((labels_insert_perm l τ rest).cons l').trans (List.Perm.swap l l' _)

theorem labels_sort_perm : ∀ fs : PFields, fs.sort.labels.Perm fs.labels
  | .nil => List.Perm.refl _
  | .cons l τ rest => (labels_insert_perm l τ _).trans ((labels_sort_perm rest).cons l)

theorem insert_increasing (l : String) (τ : PTy) : ∀ fs : PFields, l ∉ fs.labels →
    fs.labels.Pairwise (· < ·) → (PFields.insert l τ fs).labels.Pairwise (· < ·)
  | .nil, _, _ => by simp [PFields.insert, PFields.labels]
  | .cons l' τ' rest, hn, h => by
    simp only [PFields.labels, List.mem_cons, not_or] at hn
    unfold PFields.insert
    split
    · rename_i hlt
      simp only [PFields.labels] at h ⊢
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hlt
      · exact String.lt_trans hlt ((List.pairwise_cons.mp h).1 a ha)
    · rename_i hlt
      have hgt : l' < l := by
        apply Classical.byContradiction
        intro hc
        exact hn.1 (String.le_antisymm (String.not_lt.mp hc) (String.not_lt.mp hlt))
      simp only [PFields.labels] at h ⊢
      have h' := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, insert_increasing l τ rest hn.2 h'.2⟩
      intro a ha
      rcases List.mem_cons.mp ((labels_insert_perm l τ rest).mem_iff.mp ha) with rfl | ha
      · exact hgt
      · exact h'.1 a ha

theorem sort_increasing : ∀ fs : PFields, fs.labels.Nodup → fs.sort.labels.Pairwise (· < ·)
  | .nil, _ => by simp [PFields.sort, PFields.labels]
  | .cons l τ rest, hn => by
    simp only [PFields.labels, List.nodup_cons] at hn
    exact insert_increasing l τ rest.sort (fun hm => hn.1 ((labels_sort_perm rest).mem_iff.mp hm))
      (sort_increasing rest hn.2)

theorem canonB_insert (l : String) (τ : PTy) : ∀ fs : PFields,
    (PFields.insert l τ fs).canonB = (τ.canonB && fs.canonB)
  | .nil => by simp [PFields.insert, PFields.canonB]
  | .cons l' τ' rest => by
    unfold PFields.insert
    split
    · simp [PFields.canonB]
    · simp only [PFields.canonB, canonB_insert l τ rest]
      cases τ.canonB <;> cases τ'.canonB <;> simp

theorem canonB_sort : ∀ fs : PFields, fs.sort.canonB = fs.canonB
  | .nil => rfl
  | .cons l τ rest => by simp [PFields.sort, canonB_insert, canonB_sort rest, PFields.canonB]

theorem labels_normaliseEach : ∀ fs : PFields, fs.normaliseEach.labels = fs.labels
  | .nil => rfl
  | .cons l τ rest => by simp [PFields.normaliseEach, PFields.labels, labels_normaliseEach rest]

mutual
  theorem normalise_canon : ∀ τ : PTy, τ.distinctB = true → τ.normalise.canonB = true
    | .int, _ | .float, _ | .bool, _ | .string, _ | .bytes, _ | .unit, _ | .value, _ => rfl
    | .list τ, h | .maybe τ, h | .array τ, h => by
      simp only [PTy.distinctB] at h
      simp [PTy.normalise, PTy.canonB, normalise_canon τ h]
    | .tuple2 a b, h => by
      simp only [PTy.distinctB, Bool.and_eq_true] at h
      simp [PTy.normalise, PTy.canonB, normalise_canon a h.1, normalise_canon b h.2]
    | .tuple3 a b c, h => by
      simp only [PTy.distinctB, Bool.and_eq_true] at h
      simp [PTy.normalise, PTy.canonB, normalise_canon a h.1.1, normalise_canon b h.1.2,
        normalise_canon c h.2]
    | .record fs, h => by
      simp only [PTy.distinctB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [PTy.normalise, PTy.canonB, Bool.and_eq_true]
      refine ⟨by rw [canonB_sort]; exact normaliseEach_canon fs h.2, ?_⟩
      rw [labelsIncreasing_iff]
      exact sort_increasing _ (by rw [labels_normaliseEach]; exact h.1)
  theorem normaliseEach_canon : ∀ fs : PFields, fs.distinctB = true → fs.normaliseEach.canonB = true
    | .nil, _ => rfl
    | .cons l τ rest, h => by
      simp only [PFields.distinctB, Bool.and_eq_true] at h
      simp [PFields.normaliseEach, PFields.canonB, normalise_canon τ h.1, normaliseEach_canon rest h.2]
end

/-- normalise sorts the fields of nested record types too. -/
theorem normalise_example :
    (PTy.record (.cons "b" .int (.cons "a" (.list (.record (.cons "y" .bool (.cons "x" .string .nil)))) .nil))).normalise =
      .record (.cons "a" (.list (.record (.cons "x" .string (.cons "y" .bool .nil)))) (.cons "b" .int .nil)) := by
  decide +kernel

end StandardElm.Eff
