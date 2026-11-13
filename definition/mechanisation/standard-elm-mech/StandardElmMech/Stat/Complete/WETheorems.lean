/-
  A Standard Definition of Elm? Mechanisation: refutation for W on F_e (milestone (e) of plan step 11;
  WDTheorems.lean for WE.lean's W).
-/
import StandardElmMech.Stat.Complete.WEComplete
import StandardElmMech.Stat.Complete.WDTheorems
import StandardElmMech.Stat.Complete.WETerm
namespace StandardElm.Stat.Complete
namespace WE
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)


/-! ## The annotations of a derivation -/

mutual
/-- The annotations of a phrase (of its value bindings). -/
def annsAtExp : AAtExp → List (Option (BTy × List BVar))
  | .tuple e1 e2 e3 => annsExp e1 ++ annsExp e2 ++ annsExpOpt e3
  | .record r => annsExpRowOpt r
  | .update _ _ _ r => annsExpRow r
  | .letE d e => annsDec d ++ annsExp e
  | .paren e => annsExp e
  | _ => []
def annsExpRow : AExpRow → List (Option (BTy × List BVar))
  | .field _ e rest => annsExp e ++ annsExpRowOpt rest
def annsExpRowOpt : Option AExpRow → List (Option (BTy × List BVar))
  | none => []
  | some r => annsExpRow r
def annsExp : AExp → List (Option (BTy × List BVar))
  | .atexp a => annsAtExp a
  | .app e a => annsExp e ++ annsAtExp a
  | .lam _ e => annsExp e
  | .caseE e m => annsExp e ++ annsMatch m
def annsExpOpt : Option AExp → List (Option (BTy × List BVar))
  | none => []
  | some e => annsExp e
def annsMatch : AMatch → List (Option (BTy × List BVar))
  | .mk mr rest => annsMRule mr ++ annsMatchOpt rest
def annsMatchOpt : Option AMatch → List (Option (BTy × List BVar))
  | none => []
  | some m => annsMatch m
def annsMRule : AMRule → List (Option (BTy × List BVar))
  | .mk _ e => annsExp e
def annsDec : ADec → List (Option (BTy × List BVar))
  | .val _ vb => annsValBind vb
def annsValBind : AValBind → List (Option (BTy × List BVar))
  | .var _ ann _ e rest => ann :: (annsExp e ++ annsValBindOpt rest)
  | .pat _ e => annsExp e
def annsValBindOpt : Option AValBind → List (Option (BTy × List BVar))
  | none => []
  | some vb => annsValBind vb
end

/-- Every annotation of a derivation carries W's explicit variables (`canonAnnB`): the
    derivations W's result is compared with (see WE.lean on the kinds of explicit variables). -/
def CanonAnnExp (a : AExp) : Prop := ∀ an ∈ annsExp a, canonAnnB an = true

theorem canonAnnB_of_checkAnn {C : Ctx} {ann : Option (BTy × List BVar)} {τ : Ty} (h : checkAnn C ann τ = true) :
    canonAnnB ann = true := by
  match ann, h with
  | none, _ => rfl
  | some (ty, U'), h =>
    simp only [checkAnn, newForB, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1.1]; exact canon_newU _ _

set_option hygiene false in
macro "cann_tac" : tactic => `(tactic| (simp only [annsAtExp, annsExpRow, annsExpRowOpt, annsExp, annsExpOpt,
  annsMatch, annsMatchOpt, annsMRule, annsDec, annsValBind, annsValBindOpt, List.mem_append, List.mem_cons] at han))

mutual
theorem cann_atExp (C : Ctx) : ∀ a : AAtExp, checkAtExp C a = true → ∀ an ∈ annsAtExp a, canonAnnB an = true
  | .scon _ _, _ | .var _ _ _, _ | .con _ _ _, _ | .op _ _ _, _ | .nil _, _ | .unit, _ => fun _ han => by
    simp [annsAtExp] at han
  | .tuple e1 e2 e3, h => fun an han => by
    simp only [checkAtExp, Bool.and_eq_true] at h; cann_tac
    rcases han with (han | han) | han
    · exact cann_exp C e1 h.1.1 an han
    · exact cann_exp C e2 h.1.2 an han
    · exact cann_expOpt C e3 h.2 an han
  | .record r, h => fun an han => by
    simp only [checkAtExp] at h; cann_tac; exact cann_expRowOpt C r h an han
  | .update _ _ _ r, h => fun an han => by
    simp only [checkAtExp, Bool.and_eq_true] at h; cann_tac; exact cann_expRow C r h.1.2 an han
  | .letE d e, h => fun an han => by
    simp only [checkAtExp, Bool.and_eq_true] at h; cann_tac
    rcases han with han | han
    · exact cann_dec C d h.1 an han
    · exact cann_exp _ e h.2 an han
  | .paren e, h => fun an han => by simp only [checkAtExp] at h; cann_tac; exact cann_exp C e h an han
theorem cann_expRow (C : Ctx) : ∀ r : AExpRow, checkExpRow C r = true → ∀ an ∈ annsExpRow r, canonAnnB an = true
  | .field _ e rest, h => fun an han => by
    simp only [checkExpRow, Bool.and_eq_true] at h; cann_tac
    rcases han with han | han
    · exact cann_exp C e h.1 an han
    · exact cann_expRowOpt C rest h.2 an han
theorem cann_expRowOpt (C : Ctx) : ∀ r : Option AExpRow, checkExpRowOpt C r = true →
    ∀ an ∈ annsExpRowOpt r, canonAnnB an = true
  | none, _ => fun _ han => by simp [annsExpRowOpt] at han
  | some r, h => fun an han => by simp only [checkExpRowOpt] at h; cann_tac; exact cann_expRow C r h an han
theorem cann_exp (C : Ctx) : ∀ e : AExp, checkExpS C e = true → ∀ an ∈ annsExp e, canonAnnB an = true
  | .atexp a, h => fun an han => by simp only [checkExpS] at h; cann_tac; exact cann_atExp C a h an han
  | .app e a, h => fun an han => by
    simp only [checkExpS, Bool.and_eq_true] at h; cann_tac
    rcases han with han | han
    · exact cann_exp C e h.1.1 an han
    · exact cann_atExp C a h.1.2 an han
  | .lam p e, h => fun an han => by
    simp only [checkExpS, Bool.and_eq_true] at h; cann_tac; exact cann_exp _ e h.2 an han
  | .caseE e m, h => fun an han => by
    simp only [checkExpS, Bool.and_eq_true] at h; cann_tac
    rcases han with han | han
    · exact cann_exp C e h.1.1 an han
    · exact cann_match C m h.1.2 an han
theorem cann_expOpt (C : Ctx) : ∀ e : Option AExp, checkExpOpt C e = true → ∀ an ∈ annsExpOpt e, canonAnnB an = true
  | none, _ => fun _ han => by simp [annsExpOpt] at han
  | some e, h => fun an han => by simp only [checkExpOpt] at h; cann_tac; exact cann_exp C e h an han
theorem cann_match (C : Ctx) : ∀ m : AMatch, checkMatch C m = true → ∀ an ∈ annsMatch m, canonAnnB an = true
  | .mk mr rest, h => fun an han => by
    simp only [checkMatch, Bool.and_eq_true] at h; cann_tac
    rcases han with han | han
    · exact cann_mrule C mr h.1 an han
    · exact cann_matchOpt C _ rest h.2 an han
theorem cann_matchOpt (C : Ctx) (τ : Ty) : ∀ m : Option AMatch, checkMatchOptAt C τ m = true →
    ∀ an ∈ annsMatchOpt m, canonAnnB an = true
  | none, _ => fun _ han => by simp [annsMatchOpt] at han
  | some m, h => fun an han => by
    simp only [checkMatchOptAt, Bool.and_eq_true] at h; cann_tac; exact cann_match C m h.1 an han
theorem cann_mrule (C : Ctx) : ∀ mr : AMRule, checkMRule C mr = true → ∀ an ∈ annsMRule mr, canonAnnB an = true
  | .mk p e, h => fun an han => by
    simp only [checkMRule, Bool.and_eq_true] at h; cann_tac; exact cann_exp _ e h.2 an han
theorem cann_dec (C : Ctx) : ∀ d : ADec, checkDec C d = true → ∀ an ∈ annsDec d, canonAnnB an = true
  | .val VE vb, h => fun an han => by
    simp only [checkDec, Bool.and_eq_true] at h; cann_tac; exact cann_valBind _ vb h.1 an han
theorem cann_valBind (C : Ctx) : ∀ vb : AValBind, checkValBind C vb = true → ∀ an ∈ annsValBind vb, canonAnnB an = true
  | .var _ ann τ e rest, h => fun an han => by
    simp only [checkValBind, Bool.and_eq_true] at h; cann_tac
    rcases han with rfl | han | han
    · exact canonAnnB_of_checkAnn h.1.1.1
    · exact cann_exp _ e h.1.1.2 an han
    · exact cann_valBindOpt C rest h.2 an han
  | .pat p e, h => fun an han => by
    simp only [checkValBind, Bool.and_eq_true] at h; cann_tac; exact cann_exp C e h.1.2 an han
theorem cann_valBindOpt (C : Ctx) : ∀ vb : Option AValBind, checkValBindOpt C vb = true →
    ∀ an ∈ annsValBindOpt vb, canonAnnB an = true
  | none, _ => fun _ han => by simp [annsValBindOpt] at han
  | some vb, h => fun an han => by simp only [checkValBindOpt] at h; cann_tac; exact cann_valBind C vb h an han
end

/-- Step 9's checker asks every annotation's `U'` to be `newU` (`newForB`, the erratum fixing the
    kind of an explicit variable): every derivation it accepts carries W's explicit variables. -/
theorem canonAnnExp_of_checkExp {C : Ctx} {a : AExp} (h : checkExp C a = true) : CanonAnnExp a :=
  cann_exp C a (checkExpS_of_checkExp h)

set_option hygiene false in
macro "canon_tac" : tactic => `(tactic| (intro an han; apply h an; simp [annsAtExp, annsExpRow, annsExpRowOpt,
  annsExp, annsExpOpt, annsMatch, annsMatchOpt, annsMRule, annsDec, annsValBind, annsValBindOpt, han]))

mutual
theorem tysAtExp_canon : ∀ a : AAtExp, (∀ an ∈ annsAtExp a, canonAnnB an = true) →
    tysAtExp false a = Complete.tysAtExp false a
  | .scon _ _, _ | .var _ _ _, _ | .con _ _ _, _ | .op _ _ _, _ | .nil _, _ | .unit, _ => rfl
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp, Complete.tysAtExp]
    rw [tysExp_canon e1 (by canon_tac), tysExp_canon e2 (by canon_tac), tysExpOpt_canon e3 (by canon_tac)]
  | .record r, h => by simp only [tysAtExp, Complete.tysAtExp]; rw [tysExpRowOpt_canon r (by canon_tac)]
  | .update _ _ _ r, h => by simp only [tysAtExp, Complete.tysAtExp]; rw [tysExpRow_canon r (by canon_tac)]
  | .letE d e, h => by
    simp only [tysAtExp, Complete.tysAtExp]; rw [tysDec_canon d (by canon_tac), tysExp_canon e (by canon_tac)]
  | .paren e, h => by simp only [tysAtExp, Complete.tysAtExp]; rw [tysExp_canon e (by canon_tac)]
theorem tysExpRow_canon : ∀ r : AExpRow, (∀ an ∈ annsExpRow r, canonAnnB an = true) →
    tysExpRow false r = Complete.tysExpRow false r
  | .field _ e rest, h => by
    simp only [tysExpRow, Complete.tysExpRow]; rw [tysExp_canon e (by canon_tac), tysExpRowOpt_canon rest (by canon_tac)]
theorem tysExpRowOpt_canon : ∀ r : Option AExpRow, (∀ an ∈ annsExpRowOpt r, canonAnnB an = true) →
    tysExpRowOpt false r = Complete.tysExpRowOpt false r
  | none, _ => rfl
  | some r, h => by simp only [tysExpRowOpt, Complete.tysExpRowOpt]; rw [tysExpRow_canon r (by canon_tac)]
theorem tysExp_canon : ∀ e : AExp, (∀ an ∈ annsExp e, canonAnnB an = true) →
    tysExp false e = Complete.tysExp false e
  | .atexp a, h => by simp only [tysExp, Complete.tysExp]; rw [tysAtExp_canon a (by canon_tac)]
  | .app e a, h => by
    simp only [tysExp, Complete.tysExp]; rw [tysExp_canon e (by canon_tac), tysAtExp_canon a (by canon_tac)]
  | .lam p e, h => by simp only [tysExp, Complete.tysExp]; rw [tysExp_canon e (by canon_tac)]
  | .caseE e m, h => by
    simp only [tysExp, Complete.tysExp]; rw [tysExp_canon e (by canon_tac), tysMatch_canon m (by canon_tac)]
theorem tysExpOpt_canon : ∀ e : Option AExp, (∀ an ∈ annsExpOpt e, canonAnnB an = true) →
    tysExpOpt false e = Complete.tysExpOpt false e
  | none, _ => rfl
  | some e, h => by simp only [tysExpOpt, Complete.tysExpOpt]; rw [tysExp_canon e (by canon_tac)]
theorem tysMatch_canon : ∀ m : AMatch, (∀ an ∈ annsMatch m, canonAnnB an = true) →
    tysMatch false m = Complete.tysMatch false m
  | .mk mr rest, h => by
    simp only [tysMatch, Complete.tysMatch]; rw [tysMRule_canon mr (by canon_tac), tysMatchOpt_canon rest (by canon_tac)]
theorem tysMatchOpt_canon : ∀ m : Option AMatch, (∀ an ∈ annsMatchOpt m, canonAnnB an = true) →
    tysMatchOpt false m = Complete.tysMatchOpt false m
  | none, _ => rfl
  | some m, h => by simp only [tysMatchOpt, Complete.tysMatchOpt]; rw [tysMatch_canon m (by canon_tac)]
theorem tysMRule_canon : ∀ mr : AMRule, (∀ an ∈ annsMRule mr, canonAnnB an = true) →
    tysMRule false mr = Complete.tysMRule false mr
  | .mk p e, h => by simp only [tysMRule, Complete.tysMRule]; rw [tysExp_canon e (by canon_tac)]
theorem tysDec_canon : ∀ d : ADec, (∀ an ∈ annsDec d, canonAnnB an = true) →
    tysDec false d = Complete.tysDec false d
  | .val VE vb, h => by
    simp only [tysDec, Complete.tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact tysValBind_canon vb (by canon_tac)
theorem tysValBind_canon : ∀ vb : AValBind, (∀ an ∈ annsValBind vb, canonAnnB an = true) →
    tysValBind false vb = Complete.tysValBind false vb
  | .var _ ann _ e rest, h => by
    have hc : canonAnnB ann = true := h ann (by simp [annsValBind])
    simp only [tysValBind, Complete.tysValBind, annMark_false, Complete.annMark, hc, ↓reduceIte]
    rw [tysExp_canon e (by canon_tac), tysValBindOpt_canon rest (by canon_tac)]
  | .pat p e, h => by simp only [tysValBind, Complete.tysValBind]; rw [tysExp_canon e (by canon_tac)]
theorem tysValBindOpt_canon : ∀ vb : Option AValBind, (∀ an ∈ annsValBindOpt vb, canonAnnB an = true) →
    tysValBindOpt false vb = Complete.tysValBindOpt false vb
  | none, _ => rfl
  | some vb, h => by simp only [tysValBindOpt, Complete.tysValBindOpt]; rw [tysValBind_canon vb (by canon_tac)]
end

/-! ## The statements (section 7, for F_e) -/

/-- Refutation for F_e: if W fails, no derivation exists (every derivation is canonical, without
    free `bnd` variables, and carries W's explicit variables at its annotations). -/
def WERefutation : Prop :=
  ∀ fuel C0 e, RootOKD C0 → inferExpWD fuel C0 e = .fail →
    ¬ ∃ a', checkExp C0 a' = true ∧ a'.erase = e

/-- Completeness for F_e: if such a derivation exists, W neither fails nor returns `internal`,
    and for some fuel it does not run out. -/
def WECompleteness : Prop :=
  ∀ C0 e, RootOKD C0 → (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
    (∀ fuel, inferExpWD fuel C0 e ≠ .fail ∧ inferExpWD fuel C0 e ≠ .internal) ∧
    ∃ fuel, inferExpWD fuel C0 e ≠ .outOfFuel

/-- Principality for F_e: what W returns is an instance-maximal derivation. -/
def WEPrincipality : Prop :=
  ∀ fuel C0 e a, RootOKD C0 → inferExpWD fuel C0 e = .ok a →
    checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true →
      a'.erase = a.erase → InstanceOfB C0 a' a

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
    simp only [tysValBind, annMark_false, List.nil_append, List.cons_append, List.mem_cons, List.mem_append] at h
    simp only [nodesValBind]
    refine ((CnNodes.single fun τ hτ => ?_).app (cnNodesExp _ _ e fun τ hτ => h τ (.inr (.inl (.inr hτ))))).app
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

theorem nbd_of_derivation {C0 : Ctx} {a : AExp} (h1 : NoFreeBndExp C0 a) (h2 : CanonExp C0 a) (h3 : CanonAnnExp a) :
    NBD (tysExp false a) := by
  rw [tysExp_canon a h3]
  intro τ hτ
  have := tysExp_nodes C0 [] a τ hτ
  simp only [NTys, List.mem_flatMap] at this
  obtain ⟨n, hn, hτn⟩ := this
  exact ⟨h1 n hn τ hτn, h2 n hn τ hτn⟩

/-- The main induction at the root: W does not fail when a canonical derivation exists, and
    every such derivation is an image of W's result. -/
theorem weExp_root {fuel : Nat} {C0 : Ctx} {e : BExp} {a' : AExp} (hC : RootOKD C0) (hc : checkExp C0 a' = true)
    (he : a'.erase = e) :
    OutPD (EPostD (freshAboveD C0) ⟨[], freshAboveD C0⟩ rid a')
      (wdExp fuel (rigidFromD (freshAboveD C0)) C0 e ⟨[], freshAboveD C0⟩) :=
  wExp_completeD fuel _ e C0 C0 rid _ a' (root_preD C0 hC) (checkExpS_of_checkExp hc) he
    (nbd_of_derivation (noFreeBndExp_of_checkExp hc) (canonExp_of_checkExp hc) (canonAnnExp_of_checkExp hc))

theorem fix_bnd0 {n0 : Nat} {s : RSub} (h : FixR (rigidFromD n0) s) : s.r (.bnd 0) = ([], some (.bnd 0)) :=
  fix_row (h _ (rigidFromD_bnd n0 rfl))

/-- What W returns, under the final substitution, has canonical types at its nodes when a
    canonical derivation is an image of it. -/
theorem cn_result {n0 : Nat} {C0 : Ctx} {st : WDSt} {ar a' : AExp} {T : RSub} (hi : SInvD n0 st)
    (hF : FixR (rigidFromD n0) T) (hab : AbsR T st.θ) (hs : stripExp (rsbExp T ar) = stripExp a')
    (hnb : NBD (tysExp false a')) : CnNodes (nodesExp C0 [] (rsbExp (toRS st.θ) ar)) := by
  refine cnNodesExp C0 [] _ fun τ hτ => ?_
  rw [tysExp_sbD _ (fix_bnd0 (n0 := n0) fun v hv => goodR_fix hi.good hv)] at hτ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
  refine cnB_of_rsb (s := T) ?_
  rw [absR_rsb hab]
  have : rsb T σ ∈ tysExp false (stripExp a') := by
    rw [← hs, tysExp_strip, tysExp_sbD _ (fix_bnd0 hF)]; exact List.mem_map_of_mem hσ
  rw [tysExp_strip] at this
  exact (hnb _ this).2

/-- Refutation (section 7, F_d): if W fails, no canonical derivation without free `bnd` variables
    exists. -/
theorem weRefutation : WERefutation := by
  rintro fuel C0 e hC hf ⟨a', hc, he⟩
  have h := weExp_root (fuel := fuel) hC hc he
  rw [inferExpWD_eq] at hf; unfold inferExpWDSpec at hf
  simp only at hf
  split at hf
  · rename_i τ ar st hok
    rw [hok] at h
    obtain ⟨-, hi, -, -, T, hF, -, hs⟩ := h
    split at hf
    · split at hf <;> cases hf
    · rename_i hncn
      apply hncn
      have := cn_result (C0 := C0) hi hF.fix hF.abs hs (nbd_of_derivation (noFreeBndExp_of_checkExp hc) (canonExp_of_checkExp hc) (canonAnnExp_of_checkExp hc))
      simp only [List.all_eq_true]
      exact fun nd hnd τ hτ => this nd hnd τ hτ
  · rename_i hw; rw [hw] at h; exact h
  · cases hf
  · cases hf

/-- The first half of completeness: W does not fail, for any fuel. -/
theorem inferExpWD_ne_fail {fuel : Nat} {C0 : Ctx} {e : BExp} (hC : RootOKD C0)
    (h : ∃ a', checkExp C0 a' = true ∧ a'.erase = e) :
    inferExpWD fuel C0 e ≠ .fail :=
  fun hf => weRefutation fuel C0 e hC hf h

/-- Completeness for F_d without its `internal` clause (which needs L10, soundness of W's result
    before the final check): if a canonical derivation without free `bnd` variables exists, W
    fails for no fuel, and for some fuel it does not run out. -/
theorem weCompleteness_noFail : ∀ C0 e, RootOKD C0 →
    (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
    (∀ fuel, inferExpWD fuel C0 e ≠ .fail) ∧ ∃ fuel, inferExpWD fuel C0 e ≠ .outOfFuel := by
  intro C0 e hC h
  refine ⟨fun fuel => inferExpWD_ne_fail hC h, ?_⟩
  obtain ⟨n, hn, -⟩ := inferExpWD_terminates C0 e
  exact ⟨n, hn⟩

/-- `WECompleteness` follows from the remaining clause: W's result passes the final check
    whenever a canonical derivation exists. -/
theorem weCompleteness_of_ne_internal
    (h : ∀ fuel C0 e, RootOKD C0 →
      (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
      inferExpWD fuel C0 e ≠ .internal) : WECompleteness := by
  intro C0 e hC hd
  obtain ⟨h1, h2⟩ := weCompleteness_noFail C0 e hC hd
  exact ⟨fun fuel => ⟨h1 fuel, h fuel C0 e hC hd⟩, h2⟩

/-- L12: every derivation is the image of W's result
    under a substitution fixing every variable of the root context, with the instance lists left
    out. -/
theorem inferExpWD_instance {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (hC : RootOKD C0)
    (h : inferExpWD fuel C0 e = .ok a) :
    ∀ a', checkExp C0 a' = true → a'.erase = e →
      ∃ T : RSub, FixR (rigidFromD (freshAboveD C0)) T ∧ stripExp (rsbExp T a) = stripExp a' := by
  intro a' hc he
  have hw := weExp_root (fuel := fuel) hC hc he
  rw [inferExpWD_eq] at h; unfold inferExpWDSpec at h
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

end WE

end StandardElm.Stat.Complete
