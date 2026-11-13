/-
  A Standard Definition of Elm? Mechanisation: K8, the row lemma of unification (plan step 11,
  section 8), milestone (d).

  For a substitution `s` and two records `⟨ρ1 | t1⟩`, `⟨ρ2 | t2⟩` whose images are equal and
  canonical (`mrg (s ρ1) R1 = mrg (s ρ2) R2`, sorted, with `R1`, `R2` the rows of the tails'
  images): the common fields have equal images (`back_common`); the fields of one side that the
  other lacks (`onlyL`) are supplied by the other side's tail (`back_only`); a field of a tail is
  either such a field (`back_tail_in`) or a field of the other tail (`back_tail_out`). Conversely
  (`mrg_only`), with sorted rows and equal images of the common fields, both sides completed by
  the fields they lack are the same row. The cases of (U5) are assembled from these in
  MguRRec.lean.
-/
import StandardElmMech.Stat.Complete.MguR

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-! ## Rows, labels, lookups -/

theorem mem_labs_of_mem {x : Lab × Ty} {r : Row} (h : x ∈ r) : x.1 ∈ labs r := mem_labs.mpr ⟨x.2, h⟩

theorem mem_rsbRow_labs {s : RSub} {ρ : Row} {x : Lab × Ty} (h : x ∈ rsbRow s ρ) : x.1 ∈ labs ρ := by
  rw [← labs_rsbRow s ρ]; exact mem_labs_of_mem h

theorem mem_onlyL {x : Lab × Ty} {ρ1 ρ2 : Row} : x ∈ onlyL ρ1 ρ2 ↔ x ∈ ρ1 ∧ x.1 ∉ labs ρ2 := by
  simp [onlyL]

theorem rowFind?_mem {ρ : Row} {l : Lab} {τ : Ty} : FMap.find? ρ l = some τ → (l, τ) ∈ ρ := by
  induction ρ with
  | nil => intro h; cases h
  | cons p ρ ih =>
    obtain ⟨k, x⟩ := p
    simp only [FMap.find?]
    split
    · rename_i hk; intro h; cases h; subst hk; exact List.mem_cons_self ..
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem rowFind?_of_mem {ρ : Row} {l : Lab} : l ∈ labs ρ → ∃ τ, FMap.find? ρ l = some τ := by
  induction ρ with
  | nil => intro h; simp [labs] at h
  | cons p ρ ih =>
    obtain ⟨k, x⟩ := p
    intro h
    simp only [FMap.find?]
    split
    · exact ⟨x, rfl⟩
    · rename_i hk
      simp only [labs, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hk
      · exact ih h

theorem mem_commonEqs {e : Ty × Ty} {ρ1 ρ2 : Row} :
    e ∈ commonEqs ρ1 ρ2 ↔ ∃ p ∈ ρ1, FMap.find? ρ2 p.1 = some e.2 ∧ e.1 = p.2 := by
  simp only [commonEqs, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨p, hp, τ, hf, rfl⟩; exact ⟨p, hp, hf, rfl⟩
  · rintro ⟨p, hp, hf, he⟩; exact ⟨p, hp, e.2, hf, by rw [← he]⟩

/-- The sides of a common equation are field types of the two records. -/
theorem commonEqs_fields {e : Ty × Ty} {ρ1 ρ2 : Row} (h : e ∈ commonEqs ρ1 ρ2) :
    ∃ l, (l, e.1) ∈ ρ1 ∧ (l, e.2) ∈ ρ2 := by
  obtain ⟨p, hp, hf, he⟩ := mem_commonEqs.mp h
  exact ⟨p.1, by rw [he]; exact hp, rowFind?_mem hf⟩

theorem rsbRow_eq_nil {s : RSub} {ρ : Row} : rsbRow s ρ = [] ↔ ρ = [] := by
  cases ρ with
  | nil => simp [rsbRow]
  | cons p r => obtain ⟨l, x⟩ := p; simp [rsbRow]

/-! ## The backward direction: from equal canonical images -/

section back
variable {s : RSub} {ρ1 ρ2 R1 R2 : Row}

theorem back_common (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2 := by
  intro p hp q hq hl
  have h1 : (p.1, rsb s p.2) ∈ mrg (rsbRow s ρ1) R1 := mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨p, hp, rfl⟩))
  have h2 : (q.1, rsb s q.2) ∈ mrg (rsbRow s ρ1) R1 := by
    rw [heq]; exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨q, hq, rfl⟩))
  have := sorted_unique hM h1 h2 hl
  simp only [Prod.mk.injEq] at this; exact this.2

theorem back_only (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    ∀ x ∈ rsbRow s (onlyL ρ2 ρ1), x ∈ R1 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
  have hp' := mem_onlyL.mp hp
  have : (p.1, rsb s p.2) ∈ mrg (rsbRow s ρ1) R1 := by
    rw [heq]; exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨p, hp'.1, rfl⟩))
  rcases mem_mrg.mp this with h | h
  · exact absurd (mem_rsbRow_labs h) hp'.2
  · exact h

theorem back_tail_in (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    ∀ x ∈ R1, x.1 ∈ labs ρ2 → x ∈ rsbRow s (onlyL ρ2 ρ1) := by
  intro x hx hl
  obtain ⟨τ, hτ⟩ := mem_labs.mp hl
  have hd := (sorted_of_mrg hM).2.2
  have h1 : x ∈ mrg (rsbRow s ρ1) R1 := mem_mrg.mpr (.inr hx)
  have h2 : (x.1, rsb s τ) ∈ mrg (rsbRow s ρ1) R1 := by
    rw [heq]; exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨(x.1, τ), hτ, rfl⟩))
  have e := sorted_unique hM h1 h2 rfl
  have hn : x.1 ∉ labs ρ1 := by
    intro hl1
    obtain ⟨τ1, hτ1⟩ := mem_labs.mp hl1
    exact hd _ (mem_rsbRow.mpr ⟨(x.1, τ1), hτ1, rfl⟩) x hx rfl
  rw [e]; exact mem_rsbRow.mpr ⟨(x.1, τ), mem_onlyL.mpr ⟨hτ, hn⟩, rfl⟩

theorem back_tail_out (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    ∀ x ∈ R1, x.1 ∉ labs ρ2 → x ∈ R2 := by
  intro x hx hl
  have : x ∈ mrg (rsbRow s ρ2) R2 := by rw [← heq]; exact mem_mrg.mpr (.inr hx)
  rcases mem_mrg.mp this with h | h
  · exact absurd (mem_rsbRow_labs h) hl
  · exact h

/-- The tail of a side has no label of that side. -/
theorem back_disj (hM : Sorted (mrg (rsbRow s ρ1) R1)) : ∀ x ∈ R1, x.1 ∉ labs ρ1 := by
  intro x hx hl
  obtain ⟨τ, hτ⟩ := mem_labs.mp hl
  exact (sorted_of_mrg hM).2.2 _ (mem_rsbRow.mpr ⟨(x.1, τ), hτ, rfl⟩) x hx rfl

end back

/-! ## The forward direction -/

theorem sorted_only {ρ1 ρ2 : Row} (h : Sorted ρ1) : Sorted (onlyL ρ1 ρ2) := sorted_filter _ h

theorem mrg_only {s : RSub} {ρ1 ρ2 : Row} (h1 : Sorted ρ1) (h2 : Sorted ρ2)
    (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2) :
    mrg (rsbRow s ρ1) (rsbRow s (onlyL ρ2 ρ1)) = mrg (rsbRow s ρ2) (rsbRow s (onlyL ρ1 ρ2)) := by
  have srt : ∀ {a b : Row}, Sorted a → Sorted b → Sorted (mrg (rsbRow s a) (rsbRow s (onlyL b a))) := by
    intro a b ha hb
    refine sorted_mrg ((sorted_rsbRow_iff s).mpr ha) ((sorted_rsbRow_iff s).mpr (sorted_only hb)) ?_
    intro x hx y hy hxy
    obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hy
    exact (mem_onlyL.mp hq).2 (by rw [← hxy]; exact mem_rsbRow_labs hx)
  refine sorted_ext (srt h1 h2) (srt h2 h1) fun x => ?_
  have one : ∀ {a b : Row}, Sorted b → (∀ p ∈ a, ∀ q ∈ b, p.1 = q.1 → rsb s p.2 = rsb s q.2) →
      x ∈ mrg (rsbRow s a) (rsbRow s (onlyL b a)) → x ∈ mrg (rsbRow s b) (rsbRow s (onlyL a b)) := by
    intro a b _ hab hx
    rcases mem_mrg.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
      by_cases hl : p.1 ∈ labs b
      · obtain ⟨τ, hτ⟩ := mem_labs.mp hl
        rw [hab p hp (p.1, τ) hτ rfl]
        exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨(p.1, τ), hτ, rfl⟩))
      · exact mem_mrg.mpr (.inr (mem_rsbRow.mpr ⟨p, mem_onlyL.mpr ⟨hp, hl⟩, rfl⟩))
    · obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
      exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨p, (mem_onlyL.mp hp).1, rfl⟩))
  exact ⟨one h2 hc, one h1 fun p hp q hq e => (hc q hq p hp e.symm).symm⟩

/-- The common equations unified give equal images of the common fields (the second row sorted). -/
theorem common_of_eqs {s : RSub} {ρ1 ρ2 : Row} (h2 : Sorted ρ2)
    (hu : ∀ e ∈ commonEqs ρ1 ρ2, rsb s e.1 = rsb s e.2) :
    ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2 := by
  intro p hp q hq hl
  obtain ⟨τ, hτ⟩ := rowFind?_of_mem (ρ := ρ2) (l := p.1) (by rw [hl]; exact mem_labs_of_mem hq)
  have e := sorted_unique h2 (rowFind?_mem hτ) hq hl
  have := hu (p.2, τ) (mem_commonEqs.mpr ⟨p, hp, hτ, rfl⟩)
  rw [this, show τ = q.2 from (Prod.mk.inj e).2]

theorem eqs_of_common {s : RSub} {ρ1 ρ2 : Row} (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2) :
    ∀ e ∈ commonEqs ρ1 ρ2, rsb s e.1 = rsb s e.2 := by
  intro e he
  obtain ⟨p, hp, hf, h1⟩ := mem_commonEqs.mp he
  rw [h1]; exact hc p hp (p.1, e.2) (rowFind?_mem hf) rfl

end StandardElm.Stat.Complete
