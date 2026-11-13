/-
  A Standard Definition of Elm? Mechanisation: case (C) of the record step (plan step 11,
  section 4, (U5), the last case), milestone (d): both sides lack fields of the other, and the
  tails `e1 ≠ e2` are bound, with a fresh tail `ε`, to `⟨o2 | ε⟩` and then (after the first
  binding) to `⟨o1 | ε⟩`. The factor of K8 extends a unifier by `ε ↦` the rest of the first tail
  (`rec_C_ext`, MguRBind.lean).
-/
import StandardElmMech.Stat.Complete.MguRBind

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

theorem goodR_mono {R : RRigid} {n m : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X) (h : n ≤ m) :
    GoodR R m θ E X :=
  ⟨g.keys, g.adm, g.rrec, g.idem, g.stable, fun τ hτ w hw => newB_mono h (g.old τ hτ w hw),
   fun p hp => ⟨newB_mono h (g.oldθ p hp).1, fun w hw => newB_mono h ((g.oldθ p hp).2 w hw)⟩, g.cn⟩

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {rest : Eqs} {X : List Ty} {e1 e2 : RowVar}

/-- The first binding of case (C). -/
theorem rec_C_first {F1 : Eqs} {X1 : List Ty} {θ1 : RBnd} {n1 : Nat}
    (g : GoodR R n θ ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X)
    (hb1 : bindRow R e1 (onlyL ρ2 ρ1) (some (.fresh n)) (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 (some e1) :: X) θ (n + 1)
      = .next F1 X1 θ1 n1) :
    n1 = n + 1 ∧ R (.row e1) = false ∧
    F1 = sE (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (commonEqs ρ1 ρ2 ++ rest) ∧
    X1 = sX (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (.record ρ1 (some e1) :: X) ∧
    θ1 = bindR (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) θ ∧
    GoodR R (n + 1) θ1 F1 X1 ∧
    (∀ s, (s.img (.row e1) = rsb s (.record (onlyL ρ2 ρ1) (some (.fresh n))) ∧ AbsR s θ) ↔ AbsR s θ1) ∧
    (∀ s, s.img (.row e1) = rsb s (.record (onlyL ρ2 ρ1) (some (.fresh n))) →
      (UniR s F1 X1 ↔ UniR s (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 (some e1) :: X))) := by
  obtain ⟨hR1, hocc1, hl1, rfl, rfl, rfl, hn1⟩ := bindRow_next hb1
  subst n1
  have gF := goodR_mono (goodR_rec g) (Nat.le_succ n)
  have hεfree : (toRS θ).img (.row (.fresh n)) = vty (.row (.fresh n)) := img_new g (newB_fresh_self n)
  have hst : ∀ w ∈ (Ty.record (onlyL ρ2 ρ1) (some (.fresh n))).vars,
      (toRS θ).img w = vty w ∧ newB (n + 1) w = false := by
    intro w hw
    rw [vars_record, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
      have := field_vars (t := some e2) (mem_onlyL.mp hp).1 hw
      exact ⟨g.stable _ side_r w this, newB_mono (Nat.le_succ n) (g.old _ side_r w this)⟩
    · simp only [tailVars, List.mem_singleton] at hw; subst hw; exact ⟨hεfree, newB_fresh_succ n⟩
  have hcn : cnB (Ty.record (onlyL ρ2 ρ1) (some (.fresh n))) = true :=
    cnB_record.mpr ⟨sorted_only (sorted_sides g).2, fun p hp => field_cn (g.cn _ side_r) (mem_onlyL.mp hp).1⟩
  obtain ⟨g1, ha1, hu1⟩ := bindR_good (v := .row e1) (τ := .record (onlyL ρ2 ρ1) (some (.fresh n))) hR1 ⟨_, _, rfl⟩
    (fun a h => by cases h) hocc1 hcn (fun e' he' σ hσ l' hl' => by cases he'; exact hl1 σ hσ l' hl') gF
    (g.stable _ side_l _ tail_vars) (fun w hw => (hst w hw).1) (newB_mono (Nat.le_succ n) (g.old _ side_l _ tail_vars))
    (fun w hw => (hst w hw).2)
  exact ⟨rfl, hR1, rfl, rfl, rfl, g1, ha1, hu1⟩

theorem rec_case_C {F1 : Eqs} {X1 : List Ty} {θ1 : RBnd} {n1 : Nat} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X) (hne : e1 ≠ e2)
    (hb1 : bindRow R e1 (onlyL ρ2 ρ1) (some (.fresh n)) (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 (some e1) :: X) θ (n + 1)
      = .next F1 X1 θ1 n1)
    (hb2 : bindRow R e2 (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2))
      (some (.fresh n)) F1 X1 θ1 n1 = .next E' X' θ' n') :
    GoodR R n' θ' E' X' ∧ n ≤ n' ∧ CorrR R n ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X θ E' X' θ' := by
  obtain ⟨hn1, _, hF1, hX1, hθ1, g1, ha1, hu1⟩ := rec_C_first g hb1
  subst hn1 hF1 hX1 hθ1
  obtain ⟨hR2, hocc2, hl2, rfl, rfl, rfl, hn2⟩ := bindRow_next hb2
  subst n'
  have old1 : newB n (.row e1) = false := g.old _ side_l _ tail_vars
  have hεe1 : RowVar.fresh n ≠ e1 := fun h => by rw [← h, newB_fresh_self] at old1; cases old1
  have hlX : rsb (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (.record ρ1 (some e1)) ∈
      tys (sE (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (commonEqs ρ1 ρ2 ++ rest))
        (sX (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (.record ρ1 (some e1) :: X)) :=
    tys_subst.mpr ⟨_, tys_append.mpr (.inl (tys_frame_cons.mpr (.inl rfl))), rfl⟩
  have hsub : ∀ p ∈ rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2),
      p ∈ ((one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))).rx (ρ1, some e1)).1 :=
    fields_sub_rx fun p hp => (mem_onlyL.mp hp).1
  have htl1 : ((one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))).rx (ρ1, some e1)).2 = some (.fresh n) := by
    simp only [RSub.rx, RSub.tl, one_r_self]
  have hvars : ∀ w ∈ (Ty.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2))
      (some (.fresh n))).vars, w ∈ (rsb (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (.record ρ1 (some e1))).vars := by
    intro w hw
    rw [vars_record, List.mem_append] at hw
    rw [rsb_record, vars_record, List.mem_append]
    rcases hw with hw | hw
    · obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
      exact .inl (mem_rowVarsR.mpr ⟨p, hsub p hp, hw⟩)
    · right; rw [htl1]; exact hw
  have hcn : cnB (Ty.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2))
      (some (.fresh n))) = true := by
    refine cnB_record.mpr ⟨(sorted_rsbRow_iff _).mpr (sorted_only (sorted_sides g).1), fun p hp => ?_⟩
    have := g1.cn _ hlX
    rw [rsb_record] at this
    exact field_cn this (hsub p hp)
  have hv2 : (toRS (bindR (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) θ)).img (.row e2) = vty (.row e2) := by
    rw [toRS_bindR g.rrec (show IsRec (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) from ⟨_, _, rfl⟩)
      (g.stable _ side_l _ tail_vars), img_rcomp, g.stable _ side_r _ tail_vars,
      rsb_vty, img_one_ne _ (fun h => by cases h; exact hne rfl)]
  obtain ⟨g2, ha2, hu2⟩ := bindR_good (v := .row e2) hR2 ⟨_, _, rfl⟩ (fun a h => by cases h) hocc2 hcn
    (fun e' he' σ hσ l' hl' => by cases he'; exact hl2 σ hσ l' hl') g1 hv2
    (fun w hw => g1.stable _ hlX w (hvars w hw)) (newB_mono (Nat.le_succ n) (g.old _ side_r _ tail_vars))
    (fun w hw => g1.old _ hlX w (hvars w hw))
  have hτ2 : Ty.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2)) (some (.fresh n))
      = rsb (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (.record (onlyL ρ1 ρ2) (some (.fresh n))) :=
    (rsb_one_record_ne hεe1).symm
  refine ⟨g2, Nat.le_succ n, fun s h1 h2 => ?_, fun s _ hr h1 h2 => ?_⟩
  · obtain ⟨c2, a1⟩ := (ha2 s).mpr h2
    have U1 := (hu2 s c2).mp h1
    obtain ⟨c1, a0⟩ := (ha1 s).mpr a1
    have U0 := (hu1 s c1).mp U1
    have abs1 := rcomp_one (show IsRec (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) from ⟨_, _, rfl⟩) c1
    have r1 := img_row_eq.mp c1
    have r2 : s.r e2 = s.rx (onlyL ρ1 ρ2, some (.fresh n)) := by
      rw [hτ2, rsb_absorb abs1] at c2; exact img_row_eq.mp c2
    have hc := common_of_eqs (sorted_sides g).2 (uniR_rec_common U0)
    refine ⟨uniR_rec_fwd U0 (rec_eq_iff.mpr ⟨?_, ?_⟩), a0⟩
    · simp only [RSub.tl, r1, r2, RSub.rx]
      exact fw_split (sorted_sides g).1 (sorted_sides g).2 hc _
    · simp only [RSub.tl, r1, r2, RSub.rx]
  · have ag := extR_agree (s := s) (n := n) (q := (restOf (s.r e1).1 ρ2, (s.r e1).2))
    obtain ⟨r1, r2⟩ := rec_C_ext g h1
    have U0 := uniR_agree (goodR_rec g) ag (uniR_rec_back h1)
    have A0 := absR_agree g ag h2
    have c1 := img_row_eq.mpr r1
    have A1 := (ha1 _).mp ⟨c1, A0⟩
    have U1 := (hu1 _ c1).mpr U0
    have abs1 := rcomp_one (show IsRec (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) from ⟨_, _, rfl⟩) c1
    have c2 : (extR s (.fresh n) (restOf (s.r e1).1 ρ2, (s.r e1).2)).img (.row e2) =
        rsb (extR s (.fresh n) (restOf (s.r e1).1 ρ2, (s.r e1).2))
          (.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2)) (some (.fresh n))) := by
      rw [hτ2, rsb_absorb abs1]; exact img_row_eq.mpr r2
    exact ⟨_, ag, respR_extR hr, (hu2 _ c2).mpr U1, (ha2 _).mp ⟨c2, A1⟩⟩

/-- The first binding of case (C) fails: no unifier. -/
theorem rec_C_fail1 (g : GoodR R n θ ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X)
    (ho2 : onlyL ρ2 ρ1 ≠ [])
    (hb1 : bindRow R e1 (onlyL ρ2 ρ1) (some (.fresh n)) (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 (some e1) :: X) θ (n + 1)
      = .fail) :
    ∀ s, FixR R s → UniR s ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X → False := by
  intro s hf hu
  obtain ⟨hM, heq, _⟩ := rec_of_uni hu
  cases hR : R (.row e1) with
  | true =>
    have hfix := hf _ hR; simp only [RSub.img, vty, Ty.record.injEq] at hfix
    obtain ⟨p, r, hp⟩ := List.exists_cons_of_ne_nil ho2
    have hm := back_only hM heq (p.1, rsb s p.2) (by rw [hp]; exact mem_rsbRow.mpr ⟨p, List.mem_cons_self .., rfl⟩)
    simp only [RSub.tl, hfix.1] at hm; cases hm
  | false =>
    have old1 : newB n (.row e1) = false := g.old _ side_l _ tail_vars
    have ag := extR_agree (s := s) (n := n) (q := (restOf (s.r e1).1 ρ2, (s.r e1).2))
    obtain ⟨r1, _⟩ := rec_C_ext g hu
    exact bindRow_fail_flex hb1 hR (fun h => by cases h; rw [newB_fresh_self] at old1; cases old1)
      (uniR_agree (goodR_mono (goodR_rec g) (Nat.le_refl _)) ag (uniR_rec_back hu)) r1

/-- The second binding of case (C) fails: no unifier. -/
theorem rec_C_fail2 {F1 : Eqs} {X1 : List Ty} {θ1 : RBnd} {n1 : Nat}
    (g : GoodR R n θ ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X)
    (ho1 : onlyL ρ1 ρ2 ≠ [])
    (hb1 : bindRow R e1 (onlyL ρ2 ρ1) (some (.fresh n)) (commonEqs ρ1 ρ2 ++ rest) (.record ρ1 (some e1) :: X) θ (n + 1)
      = .next F1 X1 θ1 n1)
    (hb2 : bindRow R e2 (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2))
      (some (.fresh n)) F1 X1 θ1 n1 = .fail) :
    ∀ s, FixR R s → UniR s ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) X → False := by
  intro s hf hu
  obtain ⟨hM, heq, _⟩ := rec_of_uni hu
  obtain ⟨_, _, _, _, _, _, _, hu1⟩ := rec_C_first g hb1
  have old1 : newB n (.row e1) = false := g.old _ side_l _ tail_vars
  have hεe1 : RowVar.fresh n ≠ e1 := fun h => by rw [← h, newB_fresh_self] at old1; cases old1
  cases hR : R (.row e2) with
  | true =>
    have hfix := hf _ hR; simp only [RSub.img, vty, Ty.record.injEq] at hfix
    obtain ⟨p, r, hp⟩ := List.exists_cons_of_ne_nil ho1
    have hm := back_only (bk_sym hM heq) heq.symm (p.1, rsb s p.2)
      (by rw [hp]; exact mem_rsbRow.mpr ⟨p, List.mem_cons_self .., rfl⟩)
    simp only [RSub.tl, hfix.1] at hm; cases hm
  | false =>
    have old2 : newB n (.row e2) = false := g.old _ side_r _ tail_vars
    have ag := extR_agree (s := s) (n := n) (q := (restOf (s.r e1).1 ρ2, (s.r e1).2))
    obtain ⟨r1, r2⟩ := rec_C_ext g hu
    have c1 := img_row_eq.mpr r1
    have U1 := (hu1 _ c1).mpr (uniR_agree (goodR_rec g) ag (uniR_rec_back hu))
    have abs1 := rcomp_one (show IsRec (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) from ⟨_, _, rfl⟩) c1
    refine bindRow_fail_flex hb2 hR (fun h => by cases h; rw [newB_fresh_self] at old2; cases old2) U1 ?_
    apply img_row_eq.mp
    rw [← rsb_one_record_ne hεe1, rsb_absorb abs1]; exact img_row_eq.mpr r2

end rec

end StandardElm.Stat.Complete
