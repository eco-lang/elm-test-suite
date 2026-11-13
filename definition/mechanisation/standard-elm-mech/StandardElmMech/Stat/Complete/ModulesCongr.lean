/-
  A Standard Definition of Elm? Mechanisation: the checker reads a context only through its
  lookups, its explicit variables and the membership of its free variables (milestone (f) of plan
  step 11). Two contexts with the same `U`, the same qualified and type environments and the same
  lookups in their value environments (`CEq`) check the same annotated phrases. Used to read a
  module's value declarations, checked in `C ⊕ E1 ⊕ ... ⊕ Ek`, as a nested `let`, checked in
  `C + VE1 + ... + VEk` (a modification of a finite map against a prepended binding).
-/
import StandardElmMech.Stat.Complete.Modules
import StandardElmMech.Stat.ModuleStepTypes

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Free variables of a finite map, by its lookups -/

theorem mem_tyvarsBy {K V : Type} [DecidableEq K] (f : V → List BVar) (v : BVar) :
    ∀ (L : FMap K V) (seen : List K),
      v ∈ FMap.tyvarsBy f seen L ↔ ∃ k b, k ∉ seen ∧ FMap.find? L k = some b ∧ v ∈ f b
  | [], seen => by simp [FMap.tyvarsBy]
  | (k0, b0) :: rest, seen => by
    simp only [FMap.tyvarsBy, List.mem_append, mem_tyvarsBy f v rest (k0 :: seen)]
    constructor
    · rintro (h | ⟨k, b, hk, hf, hv⟩)
      · by_cases hc : (f b0).isEmpty = true ∨ k0 ∈ seen
        · have : ((f b0).isEmpty || decide (k0 ∈ seen)) = true := by
            rcases hc with hc | hc <;> simp [hc]
          rw [this] at h; simp at h
        · have hc' : ((f b0).isEmpty || decide (k0 ∈ seen)) = false := by
            simp only [not_or] at hc; simp [hc.2]; simpa using hc.1
          rw [hc'] at h
          simp only [not_or] at hc
          exact ⟨k0, b0, hc.2, by simp [FMap.find?], by simpa using h⟩
      · simp only [List.mem_cons, not_or] at hk
        refine ⟨k, b, hk.2, ?_, hv⟩
        simp only [FMap.find?]
        simp only [show ¬ (k0 = k) from fun e => hk.1 e.symm, ↓reduceIte]; exact hf
    · rintro ⟨k, b, hk, hf, hv⟩
      simp only [FMap.find?] at hf
      by_cases e : k0 = k
      · subst e
        simp only [↓reduceIte, Option.some.injEq] at hf
        subst hf
        left
        have : ((f b0).isEmpty || decide (k0 ∈ seen)) = false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
          refine ⟨?_, hk⟩
          cases h : f b0 with
          | nil => rw [h] at hv; cases hv
          | cons _ _ => rfl
        rw [this]; simpa using hv
      · simp only [e, ↓reduceIte] at hf
        right
        exact ⟨k, b, by simp only [List.mem_cons, not_or]; exact ⟨fun e' => e e'.symm, hk⟩, hf, hv⟩

/-! ## Equivalent contexts -/

/-- Contexts the checker cannot tell apart. -/
structure CEq (C D : Ctx) : Prop where
  U : C.U = D.U
  QE : C.E.QE = D.E.QE
  TE : C.E.TE = D.E.TE
  VE : ∀ k, C.E.VE.find? k = D.E.VE.find? k

theorem CEq.refl (C : Ctx) : CEq C C := ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem CEq.lookupVal {C D : Ctx} (h : CEq C D) (lv : LongId) : C.lookupVal lv = D.lookupVal lv := by
  simp only [Ctx.lookupVal, Env.lookupVal, h.QE, h.VE]

theorem CEq.lookupTy {C D : Ctx} (h : CEq C D) (lc : LongId) : C.lookupTy lc = D.lookupTy lc := by
  simp only [Ctx.lookupTy, Env.lookupTy, h.QE, h.TE]

theorem CEq.tyvars_mem {C D : Ctx} (h : CEq C D) (v : BVar) : v ∈ C.tyvars ↔ v ∈ D.tyvars := by
  simp only [Ctx.tyvars, Env.tyvars, List.mem_append, h.QE, h.TE, h.U, ValEnv.tyvars,
    mem_tyvarsBy _ v C.E.VE, mem_tyvarsBy _ v D.E.VE, h.VE]

theorem CEq.plusVE {C D : Ctx} (h : CEq C D) (VE : ValEnv) : CEq (C.plusVE VE) (D.plusVE VE) :=
  ⟨h.U, h.QE, h.TE, fun k => by simp only [Ctx.plusVE, FMap.find?_append, h.VE]⟩

theorem CEq.plusU {C D : Ctx} (h : CEq C D) (U : List BVar) : CEq (C.plusU U) (D.plusU U) :=
  ⟨by simp only [Ctx.plusU, h.U], h.QE, h.TE, h.VE⟩

theorem diffL_congr {A A' : List BVar} (h : ∀ v, v ∈ A ↔ v ∈ A') (l : List BVar) : diffL l A = diffL l A' := by
  unfold diffL
  exact List.filter_congr fun x _ => by simp only [h x]

theorem closGroup_congr {A A' : List BVar} (h : ∀ v, v ∈ A ↔ v ∈ A') (VE : ValEnv) :
    closGroup A VE = closGroup A' VE := by
  unfold closGroup FMap.mapV
  refine List.map_congr_left fun p _ => ?_
  dsimp only
  rw [diffL_congr h, diffL_congr (A := p.2.1.tyvars ++ A) (A' := p.2.1.tyvars ++ A')
    (fun v => by simp only [List.mem_append, h v])]

theorem CEq.closG {C D : Ctx} (h : CEq C D) (VE : ValEnv) : closGroup C.tyvars VE = closGroup D.tyvars VE :=
  closGroup_congr h.tyvars_mem VE

theorem CEq.elab {C D : Ctx} (h : CEq C D) (t : Src.BTy) : elabTy C t = elabTy D t :=
  Types.elabTy_congr t ⟨h.U, fun c _ => by rw [h.lookupTy c]⟩

theorem CEq.ann {C D : Ctx} (h : CEq C D) (ann : Option (Src.BTy × List BVar)) (τ : Ty) :
    checkAnn C ann τ = checkAnn D ann τ := by
  cases ann with
  | none => rfl
  | some p =>
    obtain ⟨ty, U'⟩ := p
    show (newForB U' ty C.U && decide (elabTy (C.plusU U') ty = some τ) && U'.all fun v => !decide (v ∈ C.tyvars)) =
      (newForB U' ty D.U && decide (elabTy (D.plusU U') ty = some τ) && U'.all fun v => !decide (v ∈ D.tyvars))
    rw [h.U, (h.plusU U').elab ty]
    congr 1
    exact List.all_congr rfl fun v => by simp only [decide_eq_decide.mpr (h.tyvars_mem v)]

/-! ## The checker -/

section
variable {C D : Ctx}

mutual
theorem cg_atPat (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) : ∀ p : AAtPat, checkAtPat C p = checkAtPat D p
  | .wild _ | .scon _ _ | .var _ _ | .unit | .nil _ => rfl
  | .con lc _ _ => by simp only [checkAtPat, hl lc]
  | .tuple p1 p2 p3 => by simp only [checkAtPat, cg_pat hl p1, cg_pat hl p2, cg_patOpt hl p3]
  | .record row _ => by simp only [checkAtPat, cg_patRowOpt hl row]
  | .paren p => by simp only [checkAtPat, cg_pat hl p]
theorem cg_patRow (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) : ∀ r : APatRow, checkPatRow C r = checkPatRow D r
  | .field _ _ rest => by simp only [checkPatRow, cg_patRowOpt hl rest]
theorem cg_patRowOpt (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) :
    ∀ r : Option APatRow, checkPatRowOpt C r = checkPatRowOpt D r
  | none => rfl
  | some r => by simp only [checkPatRowOpt, cg_patRow hl r]
theorem cg_pat (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) : ∀ p : APat, checkPat C p = checkPat D p
  | .atpat a => by simp only [checkPat, cg_atPat hl a]
  | .con lc _ args _ => by simp only [checkPat, hl lc, cg_atPatList hl args]
  | .cons p1 p2 => by simp only [checkPat, cg_pat hl p1, cg_pat hl p2]
  | .as p _ => by simp only [checkPat, cg_pat hl p]
theorem cg_patOpt (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) : ∀ p : Option APat, checkPatOpt C p = checkPatOpt D p
  | none => rfl
  | some p => by simp only [checkPatOpt, cg_pat hl p]
theorem cg_atPatList (hl : ∀ lv, C.lookupVal lv = D.lookupVal lv) :
    ∀ l : List AAtPat, checkAtPatList C l = checkAtPatList D l
  | [] => rfl
  | a :: as => by simp only [checkAtPatList, cg_atPat hl a, cg_atPatList hl as]
end

end

mutual
theorem cg_atExp : ∀ (a : AAtExp) {C D : Ctx}, CEq C D → checkAtExp C a = checkAtExp D a
  | .scon _ _, _, _, _ | .unit, _, _, _ | .nil _, _, _, _ => rfl
  | .var lv _ _, _, _, h => by simp only [checkAtExp, h.lookupVal lv]
  | .con lc _ _, _, _, h => by simp only [checkAtExp, h.lookupVal lc]
  | .op _ _ _, _, _, _ => rfl
  | .tuple e1 e2 e3, _, _, h => by simp only [checkAtExp, cg_expS e1 h, cg_expS e2 h, cg_expOpt e3 h]
  | .record row, _, _, h => by simp only [checkAtExp, cg_expRowOpt row h]
  | .update x _ _ row, _, _, h => by simp only [checkAtExp, h.lookupVal ⟨none, x⟩, cg_expRow row h]
  | .letE d e, C, D, h => by
    have hr : d.result C = d.result D := by
      cases d with
      | val VE vb => exact h.closG VE
    simp only [checkAtExp, cg_dec d h, hr, cg_expS e (h.plusVE (d.result D))]
  | .paren e, _, _, h => by simp only [checkAtExp, cg_expS e h]
theorem cg_expRow : ∀ (r : AExpRow) {C D : Ctx}, CEq C D → checkExpRow C r = checkExpRow D r
  | .field _ e rest, _, _, h => by simp only [checkExpRow, cg_expS e h, cg_expRowOpt rest h]
theorem cg_expRowOpt : ∀ (r : Option AExpRow) {C D : Ctx}, CEq C D → checkExpRowOpt C r = checkExpRowOpt D r
  | none, _, _, _ => rfl
  | some r, _, _, h => by simp only [checkExpRowOpt, cg_expRow r h]
theorem cg_expS : ∀ (e : AExp) {C D : Ctx}, CEq C D → checkExpS C e = checkExpS D e
  | .atexp a, _, _, h => by simp only [checkExpS, cg_atExp a h]
  | .app e a, _, _, h => by simp only [checkExpS, cg_expS e h, cg_atExp a h]
  | .lam p e, _, _, h => by simp only [checkExpS, cg_atPat h.lookupVal p, cg_expS e (h.plusVE p.ve)]
  | .caseE e m, _, _, h => by simp only [checkExpS, cg_expS e h, cg_match m h]
theorem cg_expOpt : ∀ (e : Option AExp) {C D : Ctx}, CEq C D → checkExpOpt C e = checkExpOpt D e
  | none, _, _, _ => rfl
  | some e, _, _, h => by simp only [checkExpOpt, cg_expS e h]
theorem cg_match : ∀ (m : AMatch) {C D : Ctx}, CEq C D → checkMatch C m = checkMatch D m
  | .mk mr rest, _, _, h => by simp only [checkMatch, cg_mrule mr h, cg_matchOpt rest h]
theorem cg_matchOpt : ∀ (m : Option AMatch) {C D : Ctx} {τ : Ty}, CEq C D → checkMatchOptAt C τ m = checkMatchOptAt D τ m
  | none, _, _, _, _ => rfl
  | some m, _, _, _, h => by simp only [checkMatchOptAt, cg_match m h]
theorem cg_mrule : ∀ (mr : AMRule) {C D : Ctx}, CEq C D → checkMRule C mr = checkMRule D mr
  | .mk p e, _, _, h => by simp only [checkMRule, cg_pat h.lookupVal p, cg_expS e (h.plusVE p.ve)]
theorem cg_dec : ∀ (d : ADec) {C D : Ctx}, CEq C D → checkDec C d = checkDec D d
  | .val VE vb, _, _, h => by simp only [checkDec, cg_valBind vb (h.plusVE VE)]
theorem cg_valBind : ∀ (vb : AValBind) {C D : Ctx}, CEq C D → checkValBind C vb = checkValBind D vb
  | .var _ ann τ e rest, _, _, h => by
    simp only [checkValBind, h.ann ann τ, cg_expS e (h.plusU (annU ann)), cg_valBindOpt rest h]
  | .pat p e, _, _, h => by simp only [checkValBind, cg_atPat h.lookupVal p, cg_expS e h]
theorem cg_valBindOpt : ∀ (vb : Option AValBind) {C D : Ctx}, CEq C D → checkValBindOpt C vb = checkValBindOpt D vb
  | none, _, _, _ => rfl
  | some vb, _, _, h => by simp only [checkValBindOpt, cg_valBind vb h]
end

/-! ## A module's context against a `let` body's -/

theorem modify_nil {K V : Type} [DecidableEq K] (f : FMap K V) : FMap.modify f [] = f := by
  simp [FMap.modify, FMap.keys]

/-- After a top-level group: `C ⊕ VE` against `D + VE`. -/
theorem CEq.oplus_plus {C D : Ctx} (h : CEq C D) (VE : ValEnv) :
    CEq (C.oplusE (Env.ofVE VE)) (D.plusVE VE) :=
  ⟨h.U, by simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil, Ctx.plusVE, h.QE],
    by simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil, Ctx.plusVE, h.TE],
    fun k => by simp only [Ctx.oplusE, Env.plus, Env.ofVE, Ctx.plusVE, FMap.find?_modify, FMap.find?_append, h.VE]⟩

end MW
end StandardElm.Stat.Complete
