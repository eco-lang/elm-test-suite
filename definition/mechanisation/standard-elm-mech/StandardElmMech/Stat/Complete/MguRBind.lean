/-
  A Standard Definition of Elm? Mechanisation: the record step's bindings (plan step 11,
  section 4, (U5)), milestone (d): one tail bound (`rec_case_B`), and both tails bound to the
  fields they lack and one fresh tail (`rec_case_C`, with its failures `rec_C_fail1`,
  `rec_C_fail2`), from the row lemmas of MguRCases.lean.
-/
import StandardElmMech.Stat.Complete.MguRRec

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {t1 t2 : Option RowVar} {rest : Eqs} {X : List Ty}

theorem side_l : Ty.record ρ1 t1 ∈ tys ((.record ρ1 t1, .record ρ2 t2) :: rest) X := tys_cons.mpr (.inl rfl)
theorem side_r : Ty.record ρ2 t2 ∈ tys ((.record ρ1 t1, .record ρ2 t2) :: rest) X := tys_cons.mpr (.inr (.inl rfl))

/-- (B): one tail bound to `⟨ϱ | t⟩`, made of the fields and tails of the two sides. -/
theorem rec_case_B {e : RowVar} {ϱ : Row} {t : Option RowVar} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ ((.record ρ1 t1, .record ρ2 t2) :: rest) X)
    (hb : bindRow R e ϱ t (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 t1 :: X) θ n = .next E' X' θ' n')
    (hev : BVar.row e ∈ (Ty.record ρ1 t1).vars ∨ BVar.row e ∈ (Ty.record ρ2 t2).vars)
    (hϱ : ∀ p ∈ ϱ, p ∈ ρ1 ∨ p ∈ ρ2) (hϱs : Sorted ϱ)
    (ht : ∀ e', t = some e' → BVar.row e' ∈ (Ty.record ρ1 t1).vars ∨ BVar.row e' ∈ (Ty.record ρ2 t2).vars)
    (hfwd : ∀ s, (∀ e ∈ commonEqs ρ1 ρ2, rsb s e.1 = rsb s e.2) → s.r e = s.rx (ϱ, t) →
      rsb s (.record ρ1 t1) = rsb s (.record ρ2 t2))
    (hback : ∀ s, UniR s ((.record ρ1 t1, .record ρ2 t2) :: rest) X → s.r e = s.rx (ϱ, t)) :
    GoodR R n' θ' E' X' ∧ n ≤ n' ∧ CorrR R n ((.record ρ1 t1, .record ρ2 t2) :: rest) X θ E' X' θ' := by
  obtain ⟨hR, hocc, hl, rfl, rfl, rfl, hn⟩ := bindRow_next hb
  subst n'
  have gF := goodR_rec g
  have hvars : ∀ w ∈ (Ty.record ϱ t).vars, w ∈ (Ty.record ρ1 t1).vars ∨ w ∈ (Ty.record ρ2 t2).vars := by
    intro w hw
    rw [vars_record, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
      rcases hϱ p hp with h | h
      · exact .inl (field_vars h hw)
      · exact .inr (field_vars h hw)
    · cases t with
      | none => cases hw
      | some e' => simp only [tailVars, List.mem_singleton] at hw; subst hw; exact ht e' rfl
  have hst : ∀ w, (w ∈ (Ty.record ρ1 t1).vars ∨ w ∈ (Ty.record ρ2 t2).vars) → (toRS θ).img w = vty w ∧ newB n w = false := by
    rintro w (hw | hw)
    · exact ⟨g.stable _ side_l w hw, g.old _ side_l w hw⟩
    · exact ⟨g.stable _ side_r w hw, g.old _ side_r w hw⟩
  have hcn : cnB (Ty.record ϱ t) = true := by
    refine cnB_record.mpr ⟨hϱs, fun p hp => ?_⟩
    rcases hϱ p hp with h | h
    · exact field_cn (g.cn _ side_l) h
    · exact field_cn (g.cn _ side_r) h
  obtain ⟨g', ha, hu⟩ := bindR_good (v := .row e) (τ := .record ϱ t) hR ⟨ϱ, t, rfl⟩ (fun a h => by cases h) hocc
    hcn (fun e' he' σ hσ l' hl' => by cases he'; exact hl σ hσ l' hl') gF (hst _ hev).1
    (fun w hw => (hst w (hvars w hw)).1) (hst _ hev).2 (fun w hw => (hst w (hvars w hw)).2)
  refine ⟨g', Nat.le_refl _, fun s h1 h2 => ?_, fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, ?_, ?_⟩⟩
  · obtain ⟨e1, e2⟩ := (ha s).mpr h2
    have hU := (hu s e1).mp h1
    exact ⟨uniR_rec_fwd hU (hfwd s (uniR_rec_common hU) (img_row_eq.mp e1)), e2⟩
  · exact (hu s (img_row_eq.mpr (hback s h1))).mpr (uniR_rec_back h1)
  · exact (ha s).mp ⟨img_row_eq.mpr (hback s h1), h2⟩

/-! ## (C): both tails bound, with one fresh tail -/

/-- The extension of `s` by the image of the fresh row variable `ε`. -/
def extR (s : RSub) (ε : RowVar) (q : Row × Option RowVar) : RSub := ⟨s.t, fun e => if e = ε then q else s.r e⟩

theorem newB_fresh_self (n : Nat) : newB n (.row (.fresh n)) = true := by simp [newB]
theorem newB_fresh_succ (n : Nat) : newB (n + 1) (.row (.fresh n)) = false := by simp [newB]

theorem extR_agree {s : RSub} {n : Nat} {q : Row × Option RowVar} :
    ∀ v, newB n v = false → (extR s (.fresh n) q).img v = s.img v
  | .ty _, _ => rfl
  | .row e, hv => by
    simp only [extR, RSub.img]
    rw [if_neg]; rintro rfl; rw [newB_fresh_self] at hv; cases hv

theorem respR_extR {s : RSub} {ε : RowVar} {q : Row × Option RowVar} (h : RespR s) : RespR (extR s ε q) := h

theorem one_tl_ne {e ε : RowVar} {τ : Ty} (h : ε ≠ e) : (one (.row e) τ).tl (some ε) = ([], some ε) := by
  have := img_one_ne (v := .row e) τ (w := .row ε) (by intro h'; cases h'; exact h rfl)
  simp only [RSub.img, vty, Ty.record.injEq] at this
  exact Prod.ext this.1 this.2

theorem one_r_self {e : RowVar} {ϱ : Row} {t : Option RowVar} : (one (.row e) (.record ϱ t)).r e = (ϱ, t) := by
  have := img_one_self (v := .row e) (σ := .record ϱ t) ⟨ϱ, t, rfl⟩
  simp only [RSub.img, Ty.record.injEq] at this
  exact Prod.ext this.1 this.2

theorem rsb_one_record_ne {e ε : RowVar} {τ : Ty} {ρ : Row} (h : ε ≠ e) :
    rsb (one (.row e) τ) (.record ρ (some ε)) = .record (rsbRow (one (.row e) τ) ρ) (some ε) := by
  rw [rsb, one_tl_ne h, mrg_nil_right]

/-- The facts of case (C) for a unifier of the record equation, extended by the fresh tail. -/
theorem rec_C_ext {e1 e2 : RowVar} (g : GoodR R n θ ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X)
    {s : RSub} (hu : UniR s ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X) :
    let s' := extR s (.fresh n) (restOf (s.r e1).1 ρ2, (s.r e1).2)
    s'.r e1 = s'.rx (onlyL ρ2 ρ1, some (.fresh n)) ∧ s'.r e2 = s'.rx (onlyL ρ1 ρ2, some (.fresh n)) := by
  intro s'
  obtain ⟨hM, heq, htl⟩ := rec_of_uni hu
  obtain ⟨b1, b2⟩ := bk_split hM heq
  have ag := extR_agree (s := s) (n := n) (q := (restOf (s.r e1).1 ρ2, (s.r e1).2))
  have old1 : newB n (.row e1) = false := g.old _ side_l _ tail_vars
  have old2 : newB n (.row e2) = false := g.old _ side_r _ tail_vars
  have hrow : ∀ {ρ ρ' : Row} {t : Option RowVar}, Ty.record ρ t ∈ tys ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X →
      rsbRow s' (onlyL ρ ρ') = rsbRow s (onlyL ρ ρ') := by
    intro ρ ρ' t hm
    refine rsbRow_congr _ fun w hw => ag w (g.old _ hm w ?_)
    obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
    exact field_vars (mem_onlyL.mp hp).1 hw
  have e1' : s'.r e1 = s.r e1 := by
    have := ag (.row e1) old1; simp only [RSub.img, Ty.record.injEq] at this; exact Prod.ext this.1 this.2
  have e2' : s'.r e2 = s.r e2 := by
    have := ag (.row e2) old2; simp only [RSub.img, Ty.record.injEq] at this; exact Prod.ext this.1 this.2
  have hε : s'.r (.fresh n) = (restOf (s.r e1).1 ρ2, (s.r e1).2) := by simp [s', extR]
  refine ⟨?_, ?_⟩
  · rw [e1']; simp only [RSub.rx, RSub.tl, hε]
    rw [hrow (t := some e2) side_r]
    exact Prod.ext b1 rfl
  · rw [e2']; simp only [RSub.rx, RSub.tl, hε]
    rw [hrow (t := some e1) side_l]
    simp only [RSub.tl] at b2 htl
    exact Prod.ext b2 htl.symm

theorem fields_sub_rx {σ : RSub} {ρ o : Row} {t : Option RowVar} (h : ∀ p ∈ o, p ∈ ρ) :
    ∀ p ∈ rsbRow σ o, p ∈ (σ.rx (ρ, t)).1 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hp
  exact mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨q, h q hq, rfl⟩))

end rec

end StandardElm.Stat.Complete
