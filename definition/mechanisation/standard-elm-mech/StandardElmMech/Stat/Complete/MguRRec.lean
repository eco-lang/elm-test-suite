/-
  A Standard Definition of Elm? Mechanisation: the record step (U5) of unification with rows
  (plan step 11, section 4), milestone (d): the invariant is kept and the solution correspondence
  holds (`recStep_next`); a failure has no unifier (`recStep_fail`).
-/
import StandardElmMech.Stat.Complete.MguRCases

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-! ## Transport along agreement on the old variables -/

theorem rsb_agree {n : Nat} {s s' : RSub} (ag : ∀ v, newB n v = false → s'.img v = s.img v) {τ : Ty}
    (hτ : ∀ w ∈ τ.vars, newB n w = false) : rsb s' τ = rsb s τ :=
  rsb_congr τ fun w hw => ag w (hτ w hw)

theorem uniR_agree {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X)
    {s s' : RSub} (ag : ∀ v, newB n v = false → s'.img v = s.img v) (hu : UniR s E X) : UniR s' E X := by
  refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
  · rw [rsb_agree ag (g.old e.1 (mem_tys.mpr (.inr ⟨e, he, .inl rfl⟩))),
      rsb_agree ag (g.old e.2 (mem_tys.mpr (.inr ⟨e, he, .inr rfl⟩)))]
    exact hu.1 e he
  · rw [rsb_agree ag (g.old τ hτ)]; exact hu.2 τ hτ

theorem img_new {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X)
    {u : BVar} (hu : newB n u = true) : (toRS θ).img u = vty u := by
  rw [img_toRS g.rrec]
  cases hf : FMap.find? θ u with
  | none => rfl
  | some τ => have := (g.oldθ _ (rfind?_mem hf)).1; rw [hu] at this; cases this

theorem absR_agree {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X)
    {s s' : RSub} (ag : ∀ v, newB n v = false → s'.img v = s.img v) (ha : AbsR s θ) : AbsR s' θ := by
  intro u
  by_cases hun : newB n u = true
  · rw [img_new g hun, rsb_vty]
  · have huo : newB n u = false := by simpa using hun
    have hθu : ∀ w ∈ ((toRS θ).img u).vars, newB n w = false := by
      intro w hw
      rw [img_toRS g.rrec] at hw
      cases hf : FMap.find? θ u with
      | none => rw [hf] at hw; simp only [Option.getD_none, vars_vty, List.mem_singleton] at hw; subst hw; exact huo
      | some τ => rw [hf] at hw; exact (g.oldθ _ (rfind?_mem hf)).2 w hw
    rw [rsb_agree ag hθu, ag u huo]; exact ha u

/-! ## The problem after the common equations -/

theorem field_vars {ρ : Row} {t : Option RowVar} {p : Lab × Ty} (hp : p ∈ ρ) {w : BVar} (hw : w ∈ p.2.vars) :
    w ∈ (Ty.record ρ t).vars := by
  rw [vars_record]; exact List.mem_append_left _ (mem_rowVarsR.mpr ⟨p, hp, hw⟩)

theorem field_cn {ρ : Row} {t : Option RowVar} {p : Lab × Ty} (hc : cnB (.record ρ t) = true) (hp : p ∈ ρ) :
    cnB p.2 = true := (cnB_record.mp hc).2 p hp

theorem tail_vars {ρ : Row} {e : RowVar} : BVar.row e ∈ (Ty.record ρ (some e)).vars := by
  rw [vars_record]; simp [tailVars]

/-- A problem whose types are dominated by those of a good problem is good. -/
theorem goodR_of_dom {R : RRigid} {n : Nat} {θ : RBnd} {E E' : Eqs} {X X' : List Ty} (g : GoodR R n θ E X)
    (h : ∀ τ ∈ tys E' X', ∃ σ ∈ tys E X, (∀ w ∈ τ.vars, w ∈ σ.vars) ∧ (cnB σ = true → cnB τ = true)) :
    GoodR R n θ E' X' := by
  refine ⟨g.keys, g.adm, g.rrec, g.idem, fun τ hτ w hw => ?_, fun τ hτ w hw => ?_, g.oldθ, fun τ hτ => ?_⟩
  · obtain ⟨σ, hσ, hv, _⟩ := h τ hτ; exact g.stable σ hσ w (hv w hw)
  · obtain ⟨σ, hσ, hv, _⟩ := h τ hτ; exact g.old σ hσ w (hv w hw)
  · obtain ⟨σ, hσ, _, hc⟩ := h τ hτ; exact hc (g.cn σ hσ)

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {t1 t2 : Option RowVar} {rest : Eqs} {X : List Ty}

theorem goodR_rec (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X) :
    GoodR R n θ (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X) := by
  refine goodR_of_dom g fun τ hτ => ?_
  rcases tys_append.mp hτ with hτ | ⟨e, he, hτe⟩
  · rcases tys_frame_cons.mp hτ with rfl | hτ
    · exact ⟨_, tys_cons.mpr (.inl rfl), fun _ h => h, id⟩
    · exact ⟨τ, tys_cons.mpr (.inr (.inr hτ)), fun _ h => h, id⟩
  · obtain ⟨l', h1, h2⟩ := commonEqs_fields he
    rcases hτe with rfl | rfl
    · exact ⟨.record ρ1 t1, tys_cons.mpr (.inl rfl), fun w hw => field_vars (p := (l', e.1)) h1 hw,
        fun hc => field_cn (p := (l', e.1)) hc h1⟩
    · exact ⟨.record ρ2 t2, tys_cons.mpr (.inr (.inl rfl)), fun w hw => field_vars (p := (l', e.2)) h2 hw,
        fun hc => field_cn (p := (l', e.2)) hc h2⟩

theorem rec_eq_iff {s : RSub} : rsb s (.record ρ1 t1) = rsb s (.record ρ2 t2) ↔
    mrg (rsbRow s ρ1) (s.tl t1).1 = mrg (rsbRow s ρ2) (s.tl t2).1 ∧ (s.tl t1).2 = (s.tl t2).2 := by
  simp only [rsb, Ty.record.injEq]

theorem sorted_sides (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X) : Sorted ρ1 ∧ Sorted ρ2 :=
  ⟨(cnB_record.mp (g.cn _ (tys_cons.mpr (.inl rfl)))).1, (cnB_record.mp (g.cn _ (tys_cons.mpr (.inr (.inl rfl))))).1⟩

/-- A unifier of the record equation: the merged row is sorted, the rows and the tails equal. -/
theorem rec_of_uni {s : RSub} (hu : UniR s ((.record ρ1 t1, .record ρ2 t2) :: rest) X) :
    Sorted (mrg (rsbRow s ρ1) (s.tl t1).1) ∧ mrg (rsbRow s ρ1) (s.tl t1).1 = mrg (rsbRow s ρ2) (s.tl t2).1 ∧
      (s.tl t1).2 = (s.tl t2).2 := by
  obtain ⟨h1, h2, _⟩ := uniR_cons.mp hu
  exact ⟨(cnB_rsb_record.mp (uniR_frame h2)).1, rec_eq_iff.mp h1⟩

theorem uniR_rec_back {s : RSub} (hu : UniR s ((.record ρ1 t1, .record ρ2 t2) :: rest) X) :
    UniR s (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X) := by
  obtain ⟨_, h2, h3⟩ := uniR_cons.mp hu
  obtain ⟨hM, heq, _⟩ := rec_of_uni hu
  have hc := back_common hM heq
  have cl := uniR_frame h2
  refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact eqs_of_common hc e he
    · exact h2.1 e he
  · rcases tys_append.mp hτ with hτ | ⟨e, he, hτe⟩
    · exact h2.2 τ hτ
    · obtain ⟨l', e1, e2⟩ := commonEqs_fields he
      rcases hτe with rfl | rfl
      · exact cn_field (p := (l', e.1)) cl e1
      · exact cn_field (p := (l', e.2)) h3 e2

theorem uniR_rec_common {s : RSub} {Y : List Ty} (hu : UniR s (commonEqs ρ1 ρ2 ++ rest) Y) :
    ∀ e ∈ commonEqs ρ1 ρ2, rsb s e.1 = rsb s e.2 := fun e he => hu.1 e (List.mem_append_left _ he)

theorem uniR_rec_fwd {s : RSub} (hu : UniR s (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X))
    (he : rsb s (.record ρ1 t1) = rsb s (.record ρ2 t2)) : UniR s ((.record ρ1 t1, .record ρ2 t2) :: rest) X := by
  refine uniR_cons.mpr ⟨he, ⟨fun e h => hu.1 e (List.mem_append_right _ h), fun τ hτ => hu.2 τ (tys_append.mpr (.inl hτ))⟩, ?_⟩
  rw [← he]; exact hu.2 _ (tys_append.mpr (.inl (tys_frame_cons.mpr (.inl rfl))))

/-- (A): no binding. -/
theorem rec_case_A (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X)
    (hA : ∀ s, (∀ e ∈ commonEqs ρ1 ρ2, rsb s e.1 = rsb s e.2) → rsb s (.record ρ1 t1) = rsb s (.record ρ2 t2)) :
    GoodR R n θ (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X) ∧ n ≤ n ∧
      CorrR R n ((.record ρ1 t1, .record ρ2 t2) :: rest) X θ (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X) θ :=
  ⟨goodR_rec g, Nat.le_refl _, fun s h1 h2 => ⟨uniR_rec_fwd h1 (hA s (uniR_rec_common h1)), h2⟩,
   fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, uniR_rec_back h1, h2⟩⟩

end rec

/-! ## A row binding -/

theorem bindRow_next {R : RRigid} {e : RowVar} {ϱ : Row} {t : Option RowVar} {E : Eqs} {Y : List Ty} {θ : RBnd}
    {n : Nat} {E' : Eqs} {Y' : List Ty} {θ' : RBnd} {n' : Nat} (h : bindRow R e ϱ t E Y θ n = .next E' Y' θ' n') :
    R (.row e) = false ∧ BVar.row e ∉ (Ty.record ϱ t).vars ∧ (∀ σ ∈ tys E Y, ∀ l ∈ lacksOf e σ, l ∉ labs ϱ) ∧
    E' = sE (one (.row e) (.record ϱ t)) E ∧ Y' = sX (one (.row e) (.record ϱ t)) Y ∧
    θ' = bindR (.row e) (.record ϱ t) θ ∧ n' = n := by
  unfold bindRow at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1 h2 h3
  simp only [bindS, RStep.next.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  refine ⟨by simpa using h1, h2, ?_, rfl, rfl, rfl, rfl⟩
  intro σ hσ l hl hl'
  apply h3
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact ⟨l, hl', List.mem_flatMap.mpr ⟨σ, hσ, hl⟩⟩

theorem bindRow_fail {R : RRigid} {e : RowVar} {ϱ : Row} {t : Option RowVar} {E : Eqs} {Y : List Ty} {θ : RBnd}
    {n : Nat} (h : bindRow R e ϱ t E Y θ n = .fail) :
    R (.row e) = true ∨ BVar.row e ∈ (Ty.record ϱ t).vars ∨ ∃ σ ∈ tys E Y, ∃ l ∈ lacksOf e σ, l ∈ labs ϱ := by
  unfold bindRow at h
  split at h
  · exact .inl (by assumption)
  split at h
  · exact .inr (.inl (by assumption))
  split at h
  · rename_i h3
    simp only [List.any_eq_true, decide_eq_true_eq] at h3
    obtain ⟨l, hl, hm⟩ := h3
    obtain ⟨σ, hσ, hl'⟩ := List.mem_flatMap.mp hm
    exact .inr (.inr ⟨σ, hσ, l, hl', hl⟩)
  · simp [bindS] at h

theorem img_row_eq {s : RSub} {e : RowVar} {ϱ : Row} {t : Option RowVar} :
    s.img (.row e) = rsb s (.record ϱ t) ↔ s.r e = s.rx (ϱ, t) := by
  simp only [RSub.img, rsb_record, Ty.record.injEq]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · intro h; rw [h]; exact ⟨rfl, rfl⟩

/-- A row binding that fails on a flexible variable has no unifier satisfying it. -/
theorem bindRow_fail_flex {R : RRigid} {e : RowVar} {ϱ : Row} {t : Option RowVar} {E : Eqs} {Y : List Ty}
    {θ : RBnd} {n : Nat} (h : bindRow R e ϱ t E Y θ n = .fail) (hR : R (.row e) = false)
    (ht : t ≠ some e) {s : RSub} (hu : UniR s E Y) (hs : s.r e = s.rx (ϱ, t)) : False := by
  rcases bindRow_fail h with h1 | h1 | ⟨σ, hσ, l, hl, hlϱ⟩
  · rw [hR] at h1; cases h1
  · refine occurs_neR s h1 (fun e' => ?_) (img_row_eq.mpr hs)
    simp only [vty, Ty.record.injEq] at e'; exact ht e'.2
  · apply lacks_of_cn (hu.2 σ hσ) hl
    rw [hs]
    obtain ⟨τ, hτ⟩ := mem_labs.mp hlϱ
    exact mem_labs_of_mem (x := (l, rsb s τ)) (mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨(l, τ), hτ, rfl⟩)))

end StandardElm.Stat.Complete
