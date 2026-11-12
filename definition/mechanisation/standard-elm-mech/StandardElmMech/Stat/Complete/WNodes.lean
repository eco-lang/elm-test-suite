/-
  A Standard Definition of Elm? Mechanisation: node correspondence (plan step 11, milestone (b),
  section 9) between a derivation `x` (W's result, checked) and its image `T x`: the nodes of the
  two (instance lists left out) correspond one to one, in order, with the same paths and `U`, the
  types of the image the images of the types, and each scheme of the image no more general than
  the image of the corresponding scheme (`NRel`). The closure clause is `closE_inst`.
-/
import StandardElmMech.Stat.Complete.WNodeClos

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Types and environments of stripped and substituted phrases -/

mutual
theorem stripAtExp_ty : ∀ a : AAtExp, (stripAtExp a).ty = a.ty
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .update _ _ _ _ | .unit => rfl
  | .record r => by simp only [stripAtExp, AAtExp.ty, stripExpRowOpt_row r]
  | .tuple e1 e2 e3 => by simp only [stripAtExp, AAtExp.ty, stripExp_ty e1, stripExp_ty e2, stripExpOpt_ty e3]
  | .letE _ e => by simp only [stripAtExp, AAtExp.ty, stripExp_ty e]
  | .paren e => by simp only [stripAtExp, AAtExp.ty, stripExp_ty e]
theorem stripExpRow_row : ∀ r : AExpRow, (stripExpRow r).row = r.row
  | .field l e rest => by simp only [stripExpRow, AExpRow.row, stripExp_ty e, stripExpRowOpt_row rest]
theorem stripExpRowOpt_row : ∀ r : Option AExpRow, AExpRow.rowOpt (stripExpRowOpt r) = AExpRow.rowOpt r
  | none => rfl
  | some r => by simp only [stripExpRowOpt, AExpRow.rowOpt, stripExpRow_row r]
theorem stripExp_ty : ∀ e : AExp, (stripExp e).ty = e.ty
  | .atexp a => by simp only [stripExp, AExp.ty, stripAtExp_ty a]
  | .app e _ => by simp only [stripExp, AExp.ty, stripExp_ty e]
  | .lam p e => by simp only [stripExp, AExp.ty, stripAtPat_ty p, stripExp_ty e]
  | .caseE _ m => by simp only [stripExp, AExp.ty, stripMatch_ty m]
theorem stripExpOpt_ty : ∀ e : Option AExp, AExp.tyOpt (stripExpOpt e) = AExp.tyOpt e
  | none => rfl
  | some e => by simp only [stripExpOpt, AExp.tyOpt, stripExp_ty e]
theorem stripMatch_ty : ∀ m : AMatch, (stripMatch m).ty = m.ty
  | .mk mr _ => by simp only [stripMatch, AMatch.ty, stripMRule_ty mr]
theorem stripMRule_ty : ∀ mr : AMRule, (stripMRule mr).ty = mr.ty
  | .mk p e => by simp only [stripMRule, AMRule.ty, stripPat_ty p, stripExp_ty e]
end

theorem tupleTy_sbOpt (s : FSub) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    tupleTy (sb s τ1) (sb s τ2) (sbOpt s τ3) = sb s (tupleTy τ1 τ2 τ3) := (tupleTy_sb s τ1 τ2 τ3).symm

mutual
theorem sbAtExp_ty_chk (s : FSub) : ∀ (a : AAtExp) (C : Ctx), checkAtExp C a = true → (sbAtExp s a).ty = sb s a.ty
  | .scon _ _, _, _ | .var _ _ _, _, _ | .con _ _ _, _, _ | .op _ _ _, _, _ | .nil _, _, _ | .update _ _ _ _, _, _ => rfl
  | .unit, _, _ => rfl
  | .record r, C, h => by
    simp only [checkAtExp] at h
    simp only [sbAtExp, AAtExp.ty, sbExpRowOpt_row_chk s r C h, sb]
  | .tuple e1 e2 e3, C, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [sbAtExp, AAtExp.ty, sbExp_ty_chk s e1 C h.1.1, sbExp_ty_chk s e2 C h.1.2,
      sbExpOpt_ty_chk s e3 C h.2, tupleTy_sbOpt]
  | .letE d e, C, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [sbAtExp, AAtExp.ty, sbExp_ty_chk s e _ h.2]
  | .paren e, C, h => by
    simp only [checkAtExp] at h
    simp only [sbAtExp, AAtExp.ty, sbExp_ty_chk s e C h]
theorem sbExpRow_row_chk (s : FSub) : ∀ (r : AExpRow) (C : Ctx), checkExpRow C r = true →
    (sbExpRow s r).row = sbRow s r.row
  | .field l e rest, C, h => by
    simp only [checkExpRow, Bool.and_eq_true] at h
    simp only [sbExpRow, AExpRow.row, sbExp_ty_chk s e C h.1, sbExpRowOpt_row_chk s rest C h.2, sbRow_modify]
    rfl
theorem sbExpRowOpt_row_chk (s : FSub) : ∀ (r : Option AExpRow) (C : Ctx), checkExpRowOpt C r = true →
    AExpRow.rowOpt (sbExpRowOpt s r) = sbRow s (AExpRow.rowOpt r)
  | none, _, _ => rfl
  | some r, C, h => by
    simp only [checkExpRowOpt] at h
    simp only [sbExpRowOpt, AExpRow.rowOpt, sbExpRow_row_chk s r C h]
theorem sbExp_ty_chk (s : FSub) : ∀ (e : AExp) (C : Ctx), checkExp C e = true → (sbExp s e).ty = sb s e.ty
  | .atexp a, C, h => by
    simp only [checkExp] at h
    simp only [sbExp, AExp.ty, sbAtExp_ty_chk s a C h]
  | .app e a, C, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    obtain ⟨r, hr⟩ := fn_of_match h.2
    simp only [sbExp, AExp.ty, sbExp_ty_chk s e C h.1.1, hr, sb, Ty.cod]
  | .lam p e, C, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    simp only [sbExp, AExp.ty, sbAtPat_ty, sbExp_ty_chk s e _ h.2, sb]
  | .caseE e m, C, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    obtain ⟨r, hr⟩ := fn_of_match h.2
    simp only [sbExp, AExp.ty, sbMatch_ty_chk s m C h.1.2, hr, sb, Ty.cod]
theorem sbExpOpt_ty_chk (s : FSub) : ∀ (e : Option AExp) (C : Ctx), checkExpOpt C e = true →
    AExp.tyOpt (sbExpOpt s e) = sbOpt s (AExp.tyOpt e)
  | none, _, _ => rfl
  | some e, C, h => by
    simp only [checkExpOpt] at h
    simp only [sbExpOpt, AExp.tyOpt, sbExp_ty_chk s e C h, sbOpt]
theorem sbMatch_ty_chk (s : FSub) : ∀ (m : AMatch) (C : Ctx), checkMatch C m = true → (sbMatch s m).ty = sb s m.ty
  | .mk mr _, C, h => by
    simp only [checkMatch, Bool.and_eq_true] at h
    simp only [sbMatch, AMatch.ty, sbMRule_ty_chk s mr C h.1]
theorem sbMRule_ty_chk (s : FSub) : ∀ (mr : AMRule) (C : Ctx), checkMRule C mr = true → (sbMRule s mr).ty = sb s mr.ty
  | .mk p e, C, h => by
    simp only [checkMRule, Bool.and_eq_true] at h
    simp only [sbMRule, AMRule.ty, sbPat_ty, sbExp_ty_chk s e _ h.2, sb]
end

/-! ## The relation between corresponding nodes -/

def NRel (T : FSub) (U0 : List BVar) (n n' : Node) : Prop :=
  n.U = U0 ∧ n'.path = n.path ∧ n'.U = n.U ∧ n'.tys = n.tys.map (sb T) ∧ n'.schemes.length = n.schemes.length ∧
    ∀ i (h : i < n.schemes.length) (h' : i < n'.schemes.length) t,
      Gen n'.schemes[i] t → Gen ⟨n.schemes[i].bound, sb T n.schemes[i].body⟩ t

theorem nrel_mk {T : FSub} {U0 U U' : List BVar} {path : List Nat} {tys tys' : List Ty} {ss ss' : List Scheme}
    (hU : U = U0) (hU' : U' = U0) (h1 : tys' = tys.map (sb T)) (h2 : ss' = ss.map (sbScheme T)) :
    NRel T U0 ⟨path, U, tys, ss⟩ ⟨path, U', tys', ss'⟩ := by
  subst hU hU' h1 h2
  refine ⟨rfl, rfl, rfl, rfl, by simp, fun i h h' t hg => ?_⟩
  simp only [List.getElem_map, sbScheme] at hg; exact hg

/-- Two lists related elementwise. -/
inductive F2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : F2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → F2 R l l' → F2 R (a :: l) (b :: l')

theorem forall2_append {α β : Type} {R : α → β → Prop} {l1 l2 : List α} {l1' l2' : List β}
    (h1 : F2 R l1 l1') (h2 : F2 R l2 l2') : F2 R (l1 ++ l2) (l1' ++ l2') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem veSchemes_sb (T : FSub) (VE : ValEnv) : veSchemes (sbVE T VE) = (veSchemes VE).map (sbScheme T) := by
  simp [veSchemes, sbVE]

/-- The annotations of a chain name no explicit variable. -/
def AnnNilV : AValBind → Prop
  | .var _ ann _ _ rest => annU ann = [] ∧ (match rest with
      | none => True
      | some vb => AnnNilV vb)
  | .pat _ _ => True

theorem annNilV_of_okA {n : Nat} : ∀ vb : AValBind, OkA n (tysValBind true vb) → AnnNilV vb
  | .var _ ann _ _ rest, h => by
    simp only [tysValBind, List.cons_append] at h
    unfold AnnNilV
    refine ⟨annU_of_okA fun τ hτ => h τ (by simp [hτ]), ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annNilV_of_okA vb fun τ hτ => h τ (by simp [tysValBindOpt, hτ])
  | .pat _ _, _ => trivial

theorem annNilV_sb (T : FSub) : ∀ vb : AValBind, AnnNilV vb → AnnNilV (sbValBind T vb)
  | .var _ ann _ _ rest, h => by
    unfold AnnNilV at h ⊢
    refine ⟨h.1, ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annNilV_sb T vb h.2
  | .pat _ _, _ => trivial

theorem valbind_ve_sb (T : FSub) : ∀ vb : AValBind, AnnNilV vb → (sbValBind T vb).ve = sbVE T vb.ve
  | .var x ann τ e rest, h => by
    unfold AnnNilV at h
    simp only [sbValBind]
    unfold AValBind.ve
    rw [sbVE_modify]
    congr 1
    · simp [h.1, annScheme_nil, sbVE, sbScheme, mono]
    · cases rest with
      | none => rfl
      | some vb => exact valbind_ve_sb T vb h.2
  | .pat p e, _ => by simp only [sbValBind, AValBind.ve, sbAtPat_ve]

theorem stripValBind_ve : ∀ vb : AValBind, (stripValBind vb).ve = vb.ve
  | .var x ann τ e rest => by
    simp only [stripValBind]
    cases rest with
    | none => rfl
    | some vb => unfold AValBind.ve; simp only [stripValBindOpt, stripValBind_ve vb]
  | .pat p e => by simp only [stripValBind, AValBind.ve, stripAtPat_ve]

theorem valbind_ve_pent (w : Bool) : ∀ vb : AValBind, AnnNilV vb → ∀ q ∈ vb.ve, PEnt (tysValBind w vb) q
  | .var x ann τ e rest, h, q, hq => by
    unfold AnnNilV at h
    unfold AValBind.ve at hq
    simp only [h.1, annScheme_nil] at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      refine ⟨by split <;> rfl, rfl, fun v hv => ⟨τ, by simp [tysValBind], by split at hv <;> exact hv⟩⟩
    · cases rest with
      | none => cases hq
      | some vb =>
        exact (valbind_ve_pent w vb h.2 q hq).mono fun x hx => by simp [tysValBind, tysValBindOpt, hx]
  | .pat p e, _, q, hq => by
    simp only [AValBind.ve] at hq
    exact (atpat_ve p q hq).mono fun x hx => by simp [tysValBind, hx]

end StandardElm.Stat.Complete
