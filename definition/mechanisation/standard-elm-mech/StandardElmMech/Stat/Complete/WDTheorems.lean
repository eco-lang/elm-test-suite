/-
  A Standard Definition of Elm? Mechanisation: refutation for W with records and rows (plan
  step 11, milestone (d), section 7), from the main induction L11 (WDComplete.lean, L12).

  * `cnNodesExp`: the types at the nodes of a derivation are canonical when the types it records
    (`tysExp false`) are: the nodes' types are built from them (arrows, tuples, lists, records of
    fields, codomains).
  * `wdExp_root`: the main induction at the root context (the identity substitution, every
    variable of the root context rigid).
  * `wdRefutation : WDRefutation`: if `inferExpWD` fails, no canonical derivation without free
    `bnd` variables exists. Both failures are covered: W itself fails (L11's first claim,
    contraposed), or W's result has a non-canonical type at a node (A23: a label twice). In the
    second case every canonical derivation `a'` is an image `T` of W's result (L11), so each
    type recorded by W's result has a canonical image under `T`, and so is canonical
    (`cnB_of_rsb`); and the nodes' types are canonical when the recorded ones are.
  * `inferExpWD_ne_fail`, `wdCompleteness_noFail`: completeness but for the `internal` clause
    (`wdCompleteness_of_ne_internal`: that clause gives `WDCompleteness`); `inferExpWD_instance`: L12 for the
    result of W (every such derivation is the image of W's result by a substitution fixing the
    root context's variables, with the instance lists left out).
-/
import StandardElmMech.Stat.Complete.WDComplete
import StandardElmMech.Stat.Complete.WTheorems

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Canonical types at the nodes -/

def CnNodes (l : List Node) : Prop := ∀ nd ∈ l, ∀ τ ∈ nd.tys, cnB τ = true

theorem CnNodes.app {l1 l2 : List Node} (h1 : CnNodes l1) (h2 : CnNodes l2) : CnNodes (l1 ++ l2) := fun nd hnd => by
  rcases List.mem_append.mp hnd with h | h
  · exact h1 nd h
  · exact h2 nd h

theorem CnNodes.single {path : List Nat} {U : List BVar} {ts : List Ty} {ss : List Scheme}
    (h : ∀ τ ∈ ts, cnB τ = true) : CnNodes [⟨path, U, ts, ss⟩] := fun nd hnd => by
  simp only [List.mem_singleton] at hnd; subst hnd; exact h

macro "cn_mem " : tactic => `(tactic| (intro τ hτ; first | exact h τ (by simp_all) | skip))

mutual
theorem cnNodesAtPat (U : List BVar) (path : List Nat) : ∀ p : AAtPat, (∀ τ ∈ tysAtPat p, cnB τ = true) →
    CnNodes (nodesAtPat U path p)
  | .wild τ0, h | .scon _ τ0, h | .nil τ0, h => by
    simp only [nodesAtPat]
    refine CnNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .var x τ0, h => by
    simp only [nodesAtPat]
    refine CnNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve, mono] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .con lc inst τ0, h => by
    simp only [nodesAtPat]
    refine CnNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .unit, h => by
    simp only [nodesAtPat]
    refine CnNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; rfl
  | .tuple p1 p2 p3, h => by
    have hty := cn_atpat_ty (.tuple p1 p2 p3) h
    simp only [tysAtPat, List.mem_append] at h
    simp only [nodesAtPat]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesPat U _ p1 fun τ hτ => h τ (.inl (.inl hτ)))).app
      (cnNodesPat U _ p2 fun τ hτ => h τ (.inl (.inr hτ))) |>.app (cnNodesPatOpt U _ p3 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .record r τ0, h => by
    simp only [tysAtPat, List.mem_cons] at h
    simp only [nodesAtPat]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesPatRowOpt U _ r fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .paren p, h => by
    simp only [tysAtPat] at h
    simp only [nodesAtPat]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesPat U _ p h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_pat_ty p h
theorem cnNodesPatRowOpt (U : List BVar) (path : List Nat) : ∀ r : Option APatRow, (∀ τ ∈ tysPatRowOpt r, cnB τ = true) →
    CnNodes (nodesPatRowOpt U path r)
  | none, _ => fun _ h => nomatch h
  | some (.field l τ0 rest), h => by
    simp only [nodesPatRowOpt, nodesPatRow]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesPatRowOpt U _ rest fun τ hτ => h τ (by
      simp only [tysPatRowOpt, tysPatRow, List.mem_cons]; exact .inr hτ))
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hτ
    rcases hτ with rfl | ⟨p, hp, rfl⟩
    · exact h _ (by simp [tysPatRowOpt, tysPatRow])
    · exact h _ (mem_rowOpt_tys (r := some (.field l τ0 rest)) hp)
theorem cnNodesPat (U : List BVar) (path : List Nat) : ∀ p : APat, (∀ τ ∈ tysPat p, cnB τ = true) →
    CnNodes (nodesPat U path p)
  | .atpat a, h => by
    simp only [tysPat] at h
    simp only [nodesPat]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesAtPat U _ a h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_atpat_ty a h
  | .con lc inst args τ0, h => by
    simp only [tysPat, List.mem_cons] at h
    simp only [nodesPat]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesAtPats U path 0 args fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .cons p1 p2, h => by
    have hty := cn_pat_ty (.cons p1 p2) h
    simp only [tysPat, List.mem_append] at h
    simp only [nodesPat]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesPat U _ p1 fun τ hτ => h τ (.inl hτ))).app
      (cnNodesPat U _ p2 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .as p x, h => by
    simp only [tysPat] at h
    simp only [nodesPat]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesPat U _ p h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_pat_ty p h
theorem cnNodesPatOpt (U : List BVar) (path : List Nat) : ∀ p : Option APat, (∀ τ ∈ tysPatOpt p, cnB τ = true) →
    CnNodes (nodesPatOpt U path p)
  | none, _ => fun _ h => nomatch h
  | some p, h => by simp only [tysPatOpt] at h; simp only [nodesPatOpt]; exact cnNodesPat U path p h
theorem cnNodesAtPats (U : List BVar) (path : List Nat) : ∀ (i : Nat) (l : List AAtPat), (∀ τ ∈ tysAtPats l, cnB τ = true) →
    CnNodes (nodesAtPats U path i l)
  | _, [], _ => fun _ h => nomatch h
  | i, a :: as, h => by
    simp only [tysAtPats, List.mem_append] at h
    simp only [nodesAtPats]
    exact (cnNodesAtPat U _ a fun τ hτ => h τ (.inl hτ)).app (cnNodesAtPats U path (i + 1) as fun τ hτ => h τ (.inr hτ))
end

mutual
theorem cnNodesAtExp (C : Ctx) (path : List Nat) : ∀ a : AAtExp, (∀ τ ∈ tysAtExp false a, cnB τ = true) →
    CnNodes (nodesAtExp C path a)
  | .scon _ τ0, h | .var _ _ τ0, h | .con _ _ τ0, h | .op _ _ τ0, h | .nil τ0, h => by
    simp only [nodesAtExp]
    refine CnNodes.single fun τ hτ => ?_
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (by simp [tysAtExp])
  | .unit, _ => by
    simp only [nodesAtExp]
    refine CnNodes.single fun τ hτ => ?_
    simp only [List.mem_singleton] at hτ; subst hτ; rfl
  | .tuple e1 e2 e3, h => by
    have hty := cn_atexp_ty (.tuple e1 e2 e3) h
    simp only [tysAtExp, List.mem_append] at h
    simp only [nodesAtExp]
    refine (((CnNodes.single fun τ hτ => ?_).app (cnNodesExp C _ e1 fun τ hτ => h τ (.inl (.inl hτ)))).app
      (cnNodesExp C _ e2 fun τ hτ => h τ (.inl (.inr hτ)))).app (cnNodesExpOpt C _ e3 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .record r, h => by
    have hty := cn_atexp_ty (.record r) h
    simp only [tysAtExp] at h
    simp only [nodesAtExp]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesExpRowOpt C _ r h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .update x inst τ0 r, h => by
    simp only [tysAtExp, List.mem_cons] at h
    simp only [nodesAtExp]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesExpRow C _ r fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .letE d e, h => by
    simp only [tysAtExp, List.mem_append] at h
    simp only [nodesAtExp]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesDec C _ d fun τ hτ => h τ (.inl hτ))).app
      (cnNodesExp _ _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_exp_ty e fun τ hτ => h τ (.inr hτ)
  | .paren e, h => by
    simp only [tysAtExp] at h
    simp only [nodesAtExp]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesExp C _ e h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_exp_ty e h
theorem cnNodesExpRow (C : Ctx) (path : List Nat) : ∀ r : AExpRow, (∀ τ ∈ tysExpRow false r, cnB τ = true) →
    CnNodes (nodesExpRow C path r)
  | .field l e rest, h => by
    have hrow := cn_exprow_row (.field l e rest) h
    simp only [tysExpRow, List.mem_append] at h
    simp only [nodesExpRow]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesExp C _ e fun τ hτ => h τ (.inl hτ))).app
      (cnNodesExpRowOpt C _ rest fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_map] at hτ
    obtain ⟨p, hp, rfl⟩ := hτ
    exact hrow.2 p hp
theorem cnNodesExpRowOpt (C : Ctx) (path : List Nat) : ∀ r : Option AExpRow, (∀ τ ∈ tysExpRowOpt false r, cnB τ = true) →
    CnNodes (nodesExpRowOpt C path r)
  | none, _ => fun _ h => nomatch h
  | some r, h => by simp only [tysExpRowOpt] at h; simp only [nodesExpRowOpt]; exact cnNodesExpRow C path r h
theorem cnNodesExp (C : Ctx) (path : List Nat) : ∀ e : AExp, (∀ τ ∈ tysExp false e, cnB τ = true) →
    CnNodes (nodesExp C path e)
  | .atexp a, h => by
    simp only [tysExp] at h
    simp only [nodesExp]
    refine (CnNodes.single fun τ hτ => ?_).app (cnNodesAtExp C _ a h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_atexp_ty a h
  | .app e a, h => by
    have hty := cn_exp_ty (.app e a) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesExp C _ e fun τ hτ => h τ (.inl hτ))).app
      (cnNodesAtExp C _ a fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .lam p e, h => by
    have hty := cn_exp_ty (.lam p e) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesAtPat C.U _ p fun τ hτ => h τ (.inl hτ))).app
      (cnNodesExp _ _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .caseE e m, h => by
    have hty := cn_exp_ty (.caseE e m) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesExp C _ e fun τ hτ => h τ (.inl hτ))).app
      (cnNodesMatch C _ m fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
theorem cnNodesExpOpt (C : Ctx) (path : List Nat) : ∀ e : Option AExp, (∀ τ ∈ tysExpOpt false e, cnB τ = true) →
    CnNodes (nodesExpOpt C path e)
  | none, _ => fun _ h => nomatch h
  | some e, h => by simp only [tysExpOpt] at h; simp only [nodesExpOpt]; exact cnNodesExp C path e h
theorem cnNodesMatch (C : Ctx) (path : List Nat) : ∀ m : AMatch, (∀ τ ∈ tysMatch false m, cnB τ = true) →
    CnNodes (nodesMatch C path m)
  | .mk (.mk p e) rest, h => by
    have hty := cn_mrule_ty (.mk p e) fun τ hτ => h τ (by simp only [tysMatch, List.mem_append]; exact .inl hτ)
    simp only [tysMatch, tysMRule, List.mem_append] at h
    simp only [nodesMatch]
    refine (((CnNodes.single fun τ hτ => ?_).app (cnNodesPat C.U _ p fun τ hτ => h τ (.inl (.inl hτ)))).app
      (cnNodesExp _ _ e fun τ hτ => h τ (.inl (.inr hτ)))).app (cnNodesMatchOpt C _ rest fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
theorem cnNodesMatchOpt (C : Ctx) (path : List Nat) : ∀ m : Option AMatch, (∀ τ ∈ tysMatchOpt false m, cnB τ = true) →
    CnNodes (nodesMatchOpt C path m)
  | none, _ => fun _ h => nomatch h
  | some m, h => by simp only [tysMatchOpt] at h; simp only [nodesMatchOpt]; exact cnNodesMatch C path m h
theorem cnNodesDec (C : Ctx) (path : List Nat) : ∀ d : ADec, (∀ τ ∈ tysDec false d, cnB τ = true) →
    CnNodes (nodesDec C path d)
  | .val VE vb, h => by
    simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h
    simp only [nodesDec]
    exact (CnNodes.single fun τ hτ => by cases hτ).app (cnNodesValBind _ _ vb h)
theorem cnNodesValBind (C : Ctx) (path : List Nat) : ∀ vb : AValBind, (∀ τ ∈ tysValBind false vb, cnB τ = true) →
    CnNodes (nodesValBind C path vb)
  | .var x ann τ0 e rest, h => by
    simp only [tysValBind, annMark, List.nil_append, List.cons_append, List.mem_cons, List.mem_append] at h
    simp only [nodesValBind]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesExp _ _ e fun τ hτ => h τ (.inr (.inl hτ)))).app
      (cnNodesValBindOpt C _ rest fun τ hτ => h τ (.inr (.inr hτ)))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .pat p e, h => by
    simp only [tysValBind, List.mem_append] at h
    simp only [nodesValBind]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesAtPat C.U _ p fun τ hτ => h τ (.inl hτ))).app
      (cnNodesExp C _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact cn_atpat_ty p fun τ hτ => h τ (.inl hτ)
theorem cnNodesValBindOpt (C : Ctx) (path : List Nat) : ∀ vb : Option AValBind, (∀ τ ∈ tysValBindOpt false vb, cnB τ = true) →
    CnNodes (nodesValBindOpt C path vb)
  | none, _ => fun _ h => nomatch h
  | some vb, h => by simp only [tysValBindOpt] at h; simp only [nodesValBindOpt]; exact cnNodesValBind C path vb h
end

/-! ## The root (L12) -/

theorem fixR_rid (R : RRigid) : FixR R rid := fun v _ => img_rid v

theorem root_preD (C0 : Ctx) (hC : RootOKD C0) :
    PreD (freshAboveD C0) C0 C0 rid ⟨[], freshAboveD C0⟩ :=
  ⟨⟨Nat.le_refl _, goodR_nil _ ⟨fun _ h => by simp [tys] at h, fun _ h => by simp [tys] at h⟩⟩, root_ctxWD hC,
    root_relD (fixR_rid _), fixR_rid _, absR_nil rid, respR_rid⟩

theorem nbd_of_derivation {C0 : Ctx} {a : AExp} (h1 : NoFreeBndExp C0 a) (h2 : CanonExp C0 a) : NBD (tysExp false a) := by
  intro τ hτ
  have := tysExp_nodes C0 [] a τ hτ
  simp only [NTys, List.mem_flatMap] at this
  obtain ⟨n, hn, hτn⟩ := this
  exact ⟨h1 n hn τ hτn, h2 n hn τ hτn⟩

/-- The main induction at the root: W does not fail when a canonical derivation exists, and
    every such derivation is an image of W's result. -/
theorem wdExp_root {fuel : Nat} {C0 : Ctx} {e : BExp} {a' : AExp} (hC : RootOKD C0) (hc : checkExp C0 a' = true)
    (he : a'.erase = e) :
    OutPD (EPostD (freshAboveD C0) ⟨[], freshAboveD C0⟩ rid a')
      (wdExp fuel (rigidFromD (freshAboveD C0)) C0 e ⟨[], freshAboveD C0⟩) :=
  wExp_completeD fuel _ e C0 C0 rid _ a' (root_preD C0 hC) (checkExpS_of_checkExp hc) he
    (nbd_of_derivation (noFreeBndExp_of_checkExp hc) (canonExp_of_checkExp hc))

theorem fix_bnd0 {n0 : Nat} {s : RSub} (h : FixR (rigidFromD n0) s) : s.r (.bnd 0) = ([], some (.bnd 0)) :=
  fix_row (h _ (rigidFromD_bnd n0 rfl))

/-- What W returns, under the final substitution, has canonical types at its nodes when a
    canonical derivation is an image of it. -/
theorem cn_result {n0 : Nat} {C0 : Ctx} {st : WDSt} {ar a' : AExp} {T : RSub} (hi : SInvD n0 st)
    (hF : FixR (rigidFromD n0) T) (hab : AbsR T st.θ) (hs : stripExp (rsbExp T ar) = stripExp a')
    (hnb : NBD (tysExp false a')) : CnNodes (nodesExp C0 [] (rsbExp (toRS st.θ) ar)) := by
  refine cnNodesExp C0 [] _ fun τ hτ => ?_
  rw [tysExp_sbD false _ (fix_bnd0 (n0 := n0) fun v hv => goodR_fix hi.good hv)] at hτ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
  refine cnB_of_rsb (s := T) ?_
  rw [absR_rsb hab]
  have : rsb T σ ∈ tysExp false (stripExp a') := by
    rw [← hs, tysExp_strip, tysExp_sbD false _ (fix_bnd0 hF)]; exact List.mem_map_of_mem hσ
  rw [tysExp_strip] at this
  exact (hnb _ this).2

/-- Refutation (section 7, F_d): if W fails, no derivation (all are canonical and without free `bnd` variables)
    exists. -/
theorem wdRefutation : WDRefutation := by
  rintro fuel C0 e hC hf ⟨a', hc, he⟩
  have h := wdExp_root (fuel := fuel) hC hc he
  unfold inferExpWD at hf
  simp only at hf
  split at hf
  · rename_i τ ar st hok
    rw [hok] at h
    obtain ⟨-, hi, -, -, T, hF, -, hs⟩ := h
    split at hf
    · split at hf <;> cases hf
    · rename_i hncn
      apply hncn
      have := cn_result (C0 := C0) hi hF.fix hF.abs hs (nbd_of_derivation (noFreeBndExp_of_checkExp hc) (canonExp_of_checkExp hc))
      simp only [List.all_eq_true]
      exact fun nd hnd τ hτ => this nd hnd τ hτ
  · rename_i hw; rw [hw] at h; exact h
  · cases hf
  · cases hf

/-- The first half of completeness: W does not fail, for any fuel. -/
theorem inferExpWD_ne_fail {fuel : Nat} {C0 : Ctx} {e : BExp} (hC : RootOKD C0)
    (h : ∃ a', checkExp C0 a' = true ∧ a'.erase = e) :
    inferExpWD fuel C0 e ≠ .fail :=
  fun hf => wdRefutation fuel C0 e hC hf h

/-- Completeness for F_d without its `internal` clause (which needs L10, soundness of W's result
    before the final check): if a canonical derivation without free `bnd` variables exists, W
    fails for no fuel, and for some fuel it does not run out. -/
theorem wdCompleteness_noFail : ∀ C0 e, RootOKD C0 →
    (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
    (∀ fuel, inferExpWD fuel C0 e ≠ .fail) ∧ ∃ fuel, inferExpWD fuel C0 e ≠ .outOfFuel := by
  intro C0 e hC h
  refine ⟨fun fuel => inferExpWD_ne_fail hC h, ?_⟩
  obtain ⟨n, hn, -⟩ := inferExpWD_terminates C0 e
  exact ⟨n, hn⟩

/-- `WDCompleteness` follows from the remaining clause: W's result passes the final check
    whenever a canonical derivation exists. -/
theorem wdCompleteness_of_ne_internal
    (h : ∀ fuel C0 e, RootOKD C0 →
      (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
      inferExpWD fuel C0 e ≠ .internal) : WDCompleteness := by
  intro C0 e hC hd
  obtain ⟨h1, h2⟩ := wdCompleteness_noFail C0 e hC hd
  exact ⟨fun fuel => ⟨h1 fuel, h fuel C0 e hC hd⟩, h2⟩

/-- L12: every derivation is the image of W's result
    under a substitution fixing every variable of the root context, with the instance lists left
    out. -/
theorem inferExpWD_instance {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (hC : RootOKD C0)
    (h : inferExpWD fuel C0 e = .ok a) :
    ∀ a', checkExp C0 a' = true → a'.erase = e →
      ∃ T : RSub, FixR (rigidFromD (freshAboveD C0)) T ∧ stripExp (rsbExp T a) = stripExp a' := by
  intro a' hc he
  have hw := wdExp_root (fuel := fuel) hC hc he
  unfold inferExpWD at h
  simp only at h
  split at h
  · rename_i τ ar st hok
    split at h
    · split at h
      · cases h
        rw [hok] at hw
        obtain ⟨-, -, -, -, T, hF, -, hs⟩ := hw
        refine ⟨T, hF.fix, ?_⟩
        rw [rsbExp_sbD, comp_of_absorbsD hF.abs]; exact hs
      · cases h
    · cases h
  · cases h
  · cases h
  · cases h

end StandardElm.Stat.Complete
