/-
  A Standard Definition of Elm? Mechanisation: the cases of (U5) as statements about rows
  (K8, plan step 11 section 8), milestone (d).

  Backward (`bk_*`): from equal canonical images of `⟨ρ1 | ·⟩` and `⟨ρ2 | ·⟩` with tail rows `R1`,
  `R2`, the tails' rows are determined: a closed side forces the other tail to be the fields it
  lacks (`bk_closed`), equal label sets force equal tails (`bk_same`), one side with every label
  of the other forces the other tail to be its extra fields and its own tail (`bk_extend`), and in
  general both tails are the fields they lack and a common rest `W` (`bk_split`). Failures
  (`bk_closed_only`, `bk_same_only`): a closed side lacks nothing, and two equal tails force
  equal label sets.

  Forward (`fw_*`): sorted rows with equal images of their common fields, and tails as above,
  give equal images.
-/
import StandardElmMech.Stat.Complete.MguRRows

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

section back
variable {s : RSub} {ρ1 ρ2 R1 R2 : Row}

theorem bk_sorted_left (hM : Sorted (mrg (rsbRow s ρ1) R1)) : Sorted ρ1 :=
  (sorted_rsbRow_iff s).mp (sorted_of_mrg hM).1

theorem bk_sorted_tail (hM : Sorted (mrg (rsbRow s ρ1) R1)) : Sorted R1 := (sorted_of_mrg hM).2.1

theorem bk_sym (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    Sorted (mrg (rsbRow s ρ2) R2) := heq ▸ hM

/-- The image of the fields a side has and the other lacks is sorted. -/
theorem bk_sorted_only (hM : Sorted (mrg (rsbRow s ρ1) R1)) : Sorted (rsbRow s (onlyL ρ1 ρ2)) :=
  (sorted_rsbRow_iff s).mpr (sorted_only (bk_sorted_left hM))

/-- A closed side (`R1 = []`): the other tail is the fields the closed side has and it lacks. -/
theorem bk_closed (hM : Sorted (mrg (rsbRow s ρ1) [])) (heq : mrg (rsbRow s ρ1) [] = mrg (rsbRow s ρ2) R2) :
    R2 = rsbRow s (onlyL ρ1 ρ2) := by
  have hM2 := bk_sym hM heq
  refine sorted_ext (bk_sorted_tail hM2) (bk_sorted_only hM) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases hl : x.1 ∈ labs ρ1
    · exact back_tail_in hM2 heq.symm x hx hl
    · exact absurd (back_tail_out heq.symm x hx hl) (by simp)
  · exact back_only hM2 heq.symm x hx

theorem bk_closed_only (hM : Sorted (mrg (rsbRow s ρ1) [])) (heq : mrg (rsbRow s ρ1) [] = mrg (rsbRow s ρ2) R2) :
    onlyL ρ2 ρ1 = [] := by
  cases h : onlyL ρ2 ρ1 with
  | nil => rfl
  | cons p r =>
    have := back_only hM heq (p.1, rsb s p.2) (by rw [h]; exact mem_rsbRow.mpr ⟨p, List.mem_cons_self .., rfl⟩)
    cases this

/-- The same label sets: the same tail rows. -/
theorem bk_same (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2)
    (h1 : onlyL ρ1 ρ2 = []) (h2 : onlyL ρ2 ρ1 = []) : R1 = R2 := by
  have hM2 := bk_sym hM heq
  refine sorted_ext (bk_sorted_tail hM) (bk_sorted_tail hM2) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases hl : x.1 ∈ labs ρ2
    · have := back_tail_in hM heq x hx hl; rw [h2] at this; cases this
    · exact back_tail_out heq x hx hl
  · by_cases hl : x.1 ∈ labs ρ1
    · have := back_tail_in hM2 heq.symm x hx hl; rw [h1] at this; cases this
    · exact back_tail_out heq.symm x hx hl

/-- Equal tail rows: equal label sets. -/
theorem bk_same_only (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R1) :
    onlyL ρ1 ρ2 = [] ∧ onlyL ρ2 ρ1 = [] := by
  have hM2 := bk_sym hM heq
  have one : ∀ {a b : Row}, Sorted (mrg (rsbRow s a) R1) → mrg (rsbRow s b) R1 = mrg (rsbRow s a) R1 →
      onlyL a b = [] := by
    intro a b ha hab
    cases h : onlyL a b with
    | nil => rfl
    | cons p r =>
      have hp : (p.1, rsb s p.2) ∈ rsbRow s (onlyL a b) := by rw [h]; exact mem_rsbRow.mpr ⟨p, List.mem_cons_self .., rfl⟩
      have h1 := back_only (ρ1 := b) (ρ2 := a) (hab ▸ ha) hab _ hp
      have hpm : p ∈ onlyL a b := by rw [h]; exact List.mem_cons_self ..
      exact absurd (mem_labs_of_mem (x := p) (mem_onlyL.mp hpm).1) (back_disj ha (p.1, rsb s p.2) h1)
  exact ⟨one hM heq.symm, one hM2 heq⟩

/-- The second side has every label of the first: its tail is the first's extra fields and the
    first's tail. -/
theorem bk_extend (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2)
    (h2 : onlyL ρ2 ρ1 = []) : R2 = mrg (rsbRow s (onlyL ρ1 ρ2)) R1 := by
  have hM2 := bk_sym hM heq
  have hd : LDisj (rsbRow s (onlyL ρ1 ρ2)) R1 := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
    exact back_disj hM y hy (by rw [← hxy]; exact mem_labs_of_mem (x := p) (mem_onlyL.mp hp).1)
  refine sorted_ext (bk_sorted_tail hM2) (sorted_mrg (bk_sorted_only hM) (bk_sorted_tail hM) hd)
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases hl : x.1 ∈ labs ρ1
    · exact mem_mrg.mpr (.inl (back_tail_in hM2 heq.symm x hx hl))
    · exact mem_mrg.mpr (.inr (back_tail_out heq.symm x hx hl))
  · rcases mem_mrg.mp hx with hx | hx
    · exact back_only hM2 heq.symm x hx
    · by_cases hl : x.1 ∈ labs ρ2
      · have := back_tail_in hM heq x hx hl; rw [h2] at this; cases this
      · exact back_tail_out heq x hx hl

/-- The rest of a tail: its fields with labels outside the other side. -/
def restOf (R1 ρ2 : Row) : Row := R1.filter fun p => !decide (p.1 ∈ labs ρ2)

theorem mem_restOf {x : Lab × Ty} {R1 ρ2 : Row} : x ∈ restOf R1 ρ2 ↔ x ∈ R1 ∧ x.1 ∉ labs ρ2 := by
  simp [restOf]

/-- The general case: both tails are the fields they lack and a common rest. -/
theorem bk_split (hM : Sorted (mrg (rsbRow s ρ1) R1)) (heq : mrg (rsbRow s ρ1) R1 = mrg (rsbRow s ρ2) R2) :
    R1 = mrg (rsbRow s (onlyL ρ2 ρ1)) (restOf R1 ρ2) ∧ R2 = mrg (rsbRow s (onlyL ρ1 ρ2)) (restOf R1 ρ2) := by
  have hM2 := bk_sym hM heq
  have hW : Sorted (restOf R1 ρ2) := sorted_filter _ (bk_sorted_tail hM)
  refine ⟨sorted_ext (bk_sorted_tail hM) (sorted_mrg (bk_sorted_only hM2) hW ?_) fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    sorted_ext (bk_sorted_tail hM2) (sorted_mrg (bk_sorted_only hM) hW ?_) fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
    exact (mem_restOf.mp hy).2 (by rw [← hxy]; exact mem_labs_of_mem (x := p) (mem_onlyL.mp hp).1)
  · by_cases hl : x.1 ∈ labs ρ2
    · exact mem_mrg.mpr (.inl (back_tail_in hM heq x hx hl))
    · exact mem_mrg.mpr (.inr (mem_restOf.mpr ⟨hx, hl⟩))
  · rcases mem_mrg.mp hx with hx | hx
    · exact back_only hM heq x hx
    · exact (mem_restOf.mp hx).1
  · intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
    exact back_disj hM y (mem_restOf.mp hy).1 (by rw [← hxy]; exact mem_labs_of_mem (x := p) (mem_onlyL.mp hp).1)
  · by_cases hl : x.1 ∈ labs ρ1
    · exact mem_mrg.mpr (.inl (back_tail_in hM2 heq.symm x hx hl))
    · have h1 := back_tail_out heq.symm x hx hl
      refine mem_mrg.mpr (.inr (mem_restOf.mpr ⟨h1, fun hl2 => ?_⟩))
      exact back_disj hM2 x hx hl2
  · rcases mem_mrg.mp hx with hx | hx
    · exact back_only hM2 heq.symm x hx
    · exact back_tail_out heq x (mem_restOf.mp hx).1 (mem_restOf.mp hx).2

end back

/-! ## Forward -/

section fwd
variable {s : RSub} {ρ1 ρ2 : Row}

theorem fw_closed (h1 : Sorted ρ1) (h2 : Sorted ρ2) (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2)
    (ho : onlyL ρ2 ρ1 = []) : mrg (rsbRow s ρ1) [] = mrg (rsbRow s ρ2) (rsbRow s (onlyL ρ1 ρ2)) := by
  have := mrg_only h1 h2 hc; rw [ho] at this; exact this

theorem fw_same (h1 : Sorted ρ1) (h2 : Sorted ρ2) (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2)
    (ho1 : onlyL ρ1 ρ2 = []) (ho2 : onlyL ρ2 ρ1 = []) : rsbRow s ρ1 = rsbRow s ρ2 := by
  have := mrg_only h1 h2 hc; rw [ho1, ho2] at this; simpa [rsbRow, mrg_nil_right] using this

theorem fw_extend (h1 : Sorted ρ1) (h2 : Sorted ρ2) (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2)
    (ho : onlyL ρ2 ρ1 = []) (R : Row) :
    mrg (rsbRow s ρ1) R = mrg (rsbRow s ρ2) (mrg (rsbRow s (onlyL ρ1 ρ2)) R) := by
  have := fw_closed h1 h2 hc ho
  rw [mrg_nil_right] at this
  rw [this, mrg_assoc]

theorem fw_split (h1 : Sorted ρ1) (h2 : Sorted ρ2) (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2)
    (W : Row) :
    mrg (rsbRow s ρ1) (mrg (rsbRow s (onlyL ρ2 ρ1)) W) = mrg (rsbRow s ρ2) (mrg (rsbRow s (onlyL ρ1 ρ2)) W) := by
  rw [← mrg_assoc, ← mrg_assoc, mrg_only h1 h2 hc]

end fwd

end StandardElm.Stat.Complete
