/-
  A Standard Definition of Elm? Mechanisation: the record step (U5) as a whole (plan step 11,
  section 4), milestone (d): `recStep_next` (the invariant (I1) and the solution correspondence
  (I2)) and `recStep_fail` (I3: a failure has no unifier), case by case from MguRRec.lean,
  MguRBind.lean and MguRTwo.lean.
-/
import StandardElmMech.Stat.Complete.MguRTwo

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {rest : Eqs} {X : List Ty}

theorem flip_common {s : RSub} (hc : ∀ p ∈ ρ1, ∀ q ∈ ρ2, p.1 = q.1 → rsb s p.2 = rsb s q.2) :
    ∀ p ∈ ρ2, ∀ q ∈ ρ1, p.1 = q.1 → rsb s p.2 = rsb s q.2 :=
  fun p hp q hq e => (hc q hq p hp e.symm).symm

theorem pair_eq {q : Row × Option RowVar} {a : Row} {b : Option RowVar} (h1 : q.1 = a) (h2 : q.2 = b) : q = (a, b) :=
  Prod.ext h1 h2

theorem rsbRow_ne_nil {s : RSub} {ρ : Row} (h : ρ ≠ []) : rsbRow s ρ ≠ [] := fun e => h (rsbRow_eq_nil.mp e)

theorem mrg_ne_nil {a b : Row} (h : a ≠ []) : mrg a b ≠ [] := fun e => h (mrg_eq_nil e).1

theorem fix_row {s : RSub} {e : RowVar} (h : s.img (.row e) = vty (.row e)) : s.r e = ([], some e) := by
  simp only [RSub.img, vty, Ty.record.injEq] at h; exact Prod.ext h.1 h.2

theorem recStep_next {t1 t2 : Option RowVar} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X)
    (h : recStep R ρ1 t1 ρ2 t2 rest (.record ρ1 t1 :: X) θ n = .next E' X' θ' n') :
    GoodR R n' θ' E' X' ∧ n ≤ n' ∧ CorrR R n ((.record ρ1 t1, .record ρ2 t2) :: rest) X θ E' X' θ' := by
  obtain ⟨h1, h2⟩ := sorted_sides g
  cases t1 with
  | none =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · rename_i ho; cases h
        exact rec_case_A g fun s hu => rec_eq_iff.mpr
          ⟨by simp only [RSub.tl]; rw [fw_same h1 h2 (common_of_eqs h2 hu) ho.1 ho.2], rfl⟩
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · rename_i ho
        refine rec_case_B g h (.inr tail_vars) (fun p hp => .inl (mem_onlyL.mp hp).1) (sorted_only h1)
          (fun _ h => by cases h) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
        · simp only [RSub.tl, hs, RSub.rx, mrg_nil_right]
          have := fw_closed h1 h2 (common_of_eqs h2 hu) ho; rwa [mrg_nil_right] at this
        · simp only [RSub.tl, hs, RSub.rx]
        · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
          simp only [RSub.tl] at hM heq htl
          exact pair_eq (by rw [bk_closed hM heq]; simp only [RSub.rx, RSub.tl, mrg_nil_right]) htl.symm
      · cases h
  | some e1 =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · rename_i ho
        refine rec_case_B g h (.inl tail_vars) (fun p hp => .inr (mem_onlyL.mp hp).1) (sorted_only h2)
          (fun _ h => by cases h) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
        · simp only [RSub.tl, hs, RSub.rx, mrg_nil_right]
          have := (fw_closed h2 h1 (flip_common (common_of_eqs h2 hu)) ho).symm; rwa [mrg_nil_right] at this
        · simp only [RSub.tl, hs, RSub.rx]
        · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
          simp only [RSub.tl] at hM heq htl
          exact pair_eq (by rw [bk_closed (bk_sym hM heq) heq.symm]; simp only [RSub.rx, RSub.tl, mrg_nil_right]) htl
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · rename_i he; subst he
        split at h
        · rename_i ho; cases h
          exact rec_case_A g fun s hu => rec_eq_iff.mpr
            ⟨by simp only [RSub.tl]; rw [fw_same h1 h2 (common_of_eqs h2 hu) ho.1 ho.2], rfl⟩
        · cases h
      · rename_i hne
        split at h
        · rename_i ho2
          split at h
          · rename_i ho1
            split at h
            · -- bind e1 ↦ ⟨∅ | e2⟩
              refine rec_case_B g h (.inl tail_vars) (fun p hp => by cases hp) sorted_nil
                (fun e' he' => by cases he'; exact .inr tail_vars) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
              · simp only [RSub.tl, hs, rx_rid]; rw [fw_same h1 h2 (common_of_eqs h2 hu) ho1 ho2]
              · simp only [RSub.tl, hs, rx_rid]
              · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
                rw [rx_rid]
                exact Prod.ext (bk_same hM heq ho1 ho2) htl
            · -- bind e2 ↦ ⟨∅ | e1⟩
              refine rec_case_B g h (.inr tail_vars) (fun p hp => by cases hp) sorted_nil
                (fun e' he' => by cases he'; exact .inl tail_vars) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
              · simp only [RSub.tl, hs, rx_rid]; rw [fw_same h1 h2 (common_of_eqs h2 hu) ho1 ho2]
              · simp only [RSub.tl, hs, rx_rid]
              · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
                rw [rx_rid]
                exact Prod.ext (bk_same hM heq ho1 ho2).symm htl.symm
          · -- bind e2 ↦ ⟨o1 | e1⟩
            refine rec_case_B g h (.inr tail_vars) (fun p hp => .inl (mem_onlyL.mp hp).1) (sorted_only h1)
              (fun e' he' => by cases he'; exact .inl tail_vars) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
            · simp only [RSub.tl, hs, RSub.rx]
              exact fw_extend h1 h2 (common_of_eqs h2 hu) ho2 _
            · simp only [RSub.tl, hs, RSub.rx]
            · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
              simp only [RSub.tl] at hM heq htl
              exact Prod.ext (bk_extend hM heq ho2) htl.symm
        · rename_i ho2
          split at h
          · -- bind e1 ↦ ⟨o2 | e2⟩
            rename_i ho1
            refine rec_case_B g h (.inl tail_vars) (fun p hp => .inr (mem_onlyL.mp hp).1) (sorted_only h2)
              (fun e' he' => by cases he'; exact .inr tail_vars) (fun s hu hs => rec_eq_iff.mpr ⟨?_, ?_⟩) (fun s hu => ?_)
            · simp only [RSub.tl, hs, RSub.rx]
              exact (fw_extend h2 h1 (flip_common (common_of_eqs h2 hu)) ho1 _).symm
            · simp only [RSub.tl, hs, RSub.rx]
            · obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
              simp only [RSub.tl] at hM heq htl
              exact Prod.ext (bk_extend (bk_sym hM heq) heq.symm ho1) htl
          · split at h
            · rename_i F1 X1 θ1 n1 hb1
              exact rec_case_C g hne hb1 h
            · cases h

theorem recStep_fail {t1 t2 : Option RowVar}
    (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X)
    (h : recStep R ρ1 t1 ρ2 t2 rest (.record ρ1 t1 :: X) θ n = .fail) :
    ∀ s, FixR R s → UniR s ((.record ρ1 t1, .record ρ2 t2) :: rest) X → False := by
  intro s hf hu
  obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
  have hF := uniR_rec_back hu
  cases t1 with
  | none =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      simp only [RSub.tl] at hM heq
      split at h
      · cases h
      · rename_i ho
        exact ho ⟨bk_closed_only (bk_sym hM heq) heq.symm, bk_closed_only hM heq⟩
    | some e2 =>
      simp only [recStep] at h
      simp only [RSub.tl] at hM heq htl
      split at h
      · cases hR : R (.row e2) with
        | true => rw [fix_row (hf _ hR)] at htl; cases htl
        | false =>
          refine bindRow_fail_flex h hR (fun h => by cases h) hF ?_
          exact pair_eq (by rw [bk_closed hM heq]; simp only [RSub.rx, RSub.tl, mrg_nil_right]) htl.symm
      · rename_i ho; exact ho (bk_closed_only hM heq)
  | some e1 =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      simp only [RSub.tl] at hM heq htl
      split at h
      · cases hR : R (.row e1) with
        | true => rw [fix_row (hf _ hR)] at htl; cases htl
        | false =>
          refine bindRow_fail_flex h hR (fun h => by cases h) hF ?_
          exact pair_eq (by rw [bk_closed (bk_sym hM heq) heq.symm]; simp only [RSub.rx, RSub.tl, mrg_nil_right]) htl
      · rename_i ho; exact ho (bk_closed_only (bk_sym hM heq) heq.symm)
    | some e2 =>
      simp only [recStep] at h
      simp only [RSub.tl] at hM heq htl
      split at h
      · rename_i he; subst he
        split at h
        · cases h
        · rename_i ho; exact ho (bk_same_only hM heq)
      · rename_i hne
        split at h
        · rename_i ho2
          split at h
          · rename_i ho1
            have hsame := bk_same hM heq ho1 ho2
            split at h
            · rename_i hR1
              simp only [Bool.not_eq_true'] at hR1
              exact bindRow_fail_flex h hR1 (fun h => by cases h; exact hne rfl) hF
                (by rw [rx_rid]; exact Prod.ext hsame htl)
            · rename_i hR1
              replace hR1 : R (.row e1) = true := by simpa using hR1
              cases hR2 : R (.row e2) with
              | true =>
                have := (fix_row (hf _ hR1)).symm.trans ((Prod.ext hsame htl).trans (fix_row (hf _ hR2)))
                simp only [Prod.mk.injEq, Option.some.injEq] at this; exact hne this.2
              | false =>
                exact bindRow_fail_flex h hR2 (fun h => by cases h; exact hne rfl) hF
                  (by rw [rx_rid]; exact Prod.ext hsame.symm htl.symm)
          · rename_i ho1
            have hext := bk_extend hM heq ho2
            cases hR2 : R (.row e2) with
            | true =>
              rw [fix_row (hf _ hR2)] at hext
              exact mrg_ne_nil (rsbRow_ne_nil ho1) hext.symm
            | false =>
              exact bindRow_fail_flex h hR2 (fun h => by cases h; exact hne rfl) hF
                (by simp only [RSub.rx, RSub.tl]; exact Prod.ext hext htl.symm)
        · rename_i ho2
          split at h
          · rename_i ho1
            have hext := bk_extend (bk_sym hM heq) heq.symm ho1
            cases hR1 : R (.row e1) with
            | true =>
              rw [fix_row (hf _ hR1)] at hext
              exact mrg_ne_nil (rsbRow_ne_nil ho2) hext.symm
            | false =>
              exact bindRow_fail_flex h hR1 (fun h => by cases h; exact hne rfl) hF
                (by simp only [RSub.rx, RSub.tl]; exact Prod.ext hext htl)
          · rename_i ho1
            split at h
            · rename_i F1 X1 θ1 n1 hb1
              exact rec_C_fail2 g ho1 hb1 h s hf hu
            · rename_i hb1
              exact rec_C_fail1 g ho2 hb1 s hf hu

end rec

end StandardElm.Stat.Complete
