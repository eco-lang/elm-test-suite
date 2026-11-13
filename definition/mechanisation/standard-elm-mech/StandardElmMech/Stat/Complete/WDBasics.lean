/-
  A Standard Definition of Elm? Mechanisation: basic lemmas for the proof of completeness and
  principality of W with records and rows (`inferExpWD`, plan step 11, milestone (d), section 8:
  L1 with substitutions of type and row variables), and the outcome predicate of a run of W.

  WBasics.lean's lemmas for `RSub` (RSubst.lean):

  * Variables: `OkTD n τ`: the variables of `τ` (type or row) are not `bnd` and are below `n`
    (`newB`, MguR.lean): every type W builds is of this form (W's own row variables are fresh).
  * L1: substitution commutes with erasure, with the instance lists left out (`stripExp`), with
    the type and the value environment an annotated phrase determines, and composes (`rcomp`).
  * `OutPD P r`: the outcome `r` of W is not `fail`, and if it is `ok` it satisfies `P`.
-/
import StandardElmMech.Stat.Complete.WDUnify

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Variables -/

theorem rigidFromD_eq (n0 : Nat) (v : BVar) : rigidFromD n0 v = !newB n0 v := by
  rcases v with (a | e)
  · cases a with
    | fresh k c => simp only [rigidFromD, newB, TyVar.isNew]; by_cases h : k < n0 <;> simp [h] <;> omega
    | _ => rfl
  · cases e with
    | fresh k => simp only [rigidFromD, newB]; by_cases h : k < n0 <;> simp [h] <;> omega
    | _ => rfl

theorem rigid_of_oldD {n0 : Nat} {v : BVar} (h : newB n0 v = false) : rigidFromD n0 v = true := by
  rw [rigidFromD_eq, h]; rfl

theorem not_rigid_of_newD {n0 n : Nat} (h0 : n0 ≤ n) {v : BVar} (h : newB n v = true) :
    rigidFromD n0 v = false := by
  rw [rigidFromD_eq]
  have : newB n0 v = true := by
    cases e : newB n0 v
    · rw [newB_mono h0 e] at h; cases h
    · rfl
  rw [this]; rfl

theorem newFlexR_rigidFromD {n0 n : Nat} (h : n0 ≤ n) : NewFlexR (rigidFromD n0) n := fun _ hv => not_rigid_of_newD h hv

theorem rigidFromD_bnd (n0 : Nat) {v : BVar} (h : v.isBnd = true) : rigidFromD n0 v = true := by
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isBnd, rigidFromD]

/-- A type W builds: its variables are not `bnd`, and are below the counter. -/
def OkTD (n : Nat) (τ : Ty) : Prop := ∀ v ∈ τ.vars, v.isBnd = false ∧ newB n v = false

theorem OkTD.mono {n m : Nat} (h : n ≤ m) {τ : Ty} (hτ : OkTD n τ) : OkTD m τ := fun v hv =>
  ⟨(hτ v hv).1, newB_mono h (hτ v hv).2⟩

theorem OkTD.old {n : Nat} {τ : Ty} (h : OkTD n τ) : ∀ w ∈ τ.vars, newB n w = false := fun w hw => (h w hw).2

theorem OkT_varD {n : Nat} {a : TyVar} (h1 : BVar.isBnd (.ty a) = false) (h2 : newB n (.ty a) = false) :
    OkTD n (.var a) := by
  intro v hv; simp only [Ty.vars, List.mem_singleton] at hv; subst hv; exact ⟨h1, h2⟩

theorem OkT_vtyD {n : Nat} {v : BVar} (h1 : v.isBnd = false) (h2 : newB n v = false) : OkTD n (vty v) := by
  intro w hw; rw [vars_vty, List.mem_singleton] at hw; subst hw; exact ⟨h1, h2⟩

theorem OkT_conD {n : Nat} {t : TyName} {as : List Ty} (h : ∀ τ ∈ as, OkTD n τ) : OkTD n (.con as t) := by
  intro v hv
  simp only [Ty.vars] at hv
  obtain ⟨τ, h1, h2⟩ := mem_listVarsR.mp hv
  exact h τ h1 v h2

theorem OkT_fnD {n : Nat} {a b : Ty} (ha : OkTD n a) (hb : OkTD n b) : OkTD n (.fn a b) := by
  intro v hv; simp only [Ty.vars, List.mem_append] at hv
  rcases hv with hv | hv
  · exact ha v hv
  · exact hb v hv

theorem OkT_fn_iffD {n : Nat} {a b : Ty} : OkTD n (.fn a b) ↔ OkTD n a ∧ OkTD n b :=
  ⟨fun h => ⟨fun v hv => h v (by simp [Ty.vars, hv]), fun v hv => h v (by simp [Ty.vars, hv])⟩,
   fun ⟨ha, hb⟩ => OkT_fnD ha hb⟩

theorem OkT_recordD {n : Nat} {ρ : Row} {tl : Option RowVar} (h : ∀ p ∈ ρ, OkTD n p.2)
    (ht : ∀ v ∈ tailVars tl, v.isBnd = false ∧ newB n v = false) : OkTD n (.record ρ tl) := by
  intro v hv
  rw [vars_record, List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨p, hp, hv⟩ := mem_rowVarsR.mp hv; exact h p hp v hv
  · exact ht v hv

theorem OkT_of_vars_nilD {n : Nat} {τ : Ty} (h : τ.vars = []) : OkTD n τ := by
  intro v hv; rw [h] at hv; cases hv

theorem OkT_listD {n : Nat} {τ : Ty} (h : OkTD n τ) : OkTD n (listTy τ) :=
  OkT_conD (fun x hx => by simp at hx; subst hx; exact h)

theorem OkT_tupleD {n : Nat} {τ1 τ2 : Ty} {τ3 : Option Ty} (h1 : OkTD n τ1) (h2 : OkTD n τ2)
    (h3 : ∀ τ, τ3 = some τ → OkTD n τ) : OkTD n (tupleTy τ1 τ2 τ3) := by
  cases τ3 with
  | none => exact OkT_conD (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption)
  | some τ =>
    exact OkT_conD (fun x hx => by
      simp at hx; rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3 _ rfl)

/-- The image of an `OkTD` type under a substitution whose images of its variables are `OkTD`. -/
theorem OkT_rsbD {n : Nat} {s : RSub} {τ : Ty} (hs : ∀ w ∈ τ.vars, OkTD n (s.img w)) : OkTD n (rsb s τ) := by
  intro v hv
  obtain ⟨w, hw, hv'⟩ := (mem_vars_rsb s τ v).mp hv
  exact hs w hw v hv'

/-! ## The outcome of a run -/

/-- The outcome is not a failure, and an `ok` outcome satisfies `P`. -/
def OutPD {α : Type} (P : α → WDSt → Prop) : WDOut α → Prop
  | .ok a st => P a st
  | .fail => False
  | .unsupported => True
  | .outOfFuel => True

theorem outP_bindD {α β : Type} {m : WDM α} {f : α → WDM β} {st : WDSt} {Q : α → WDSt → Prop}
    {P : β → WDSt → Prop} (h : OutPD Q (m st)) (hf : ∀ a st', Q a st' → OutPD P (f a st')) :
    OutPD P ((m >>= f) st) := by
  show OutPD P (WDM.bind m f st)
  unfold WDM.bind
  cases hm : m st with
  | ok a st' => rw [hm] at h; exact hf a st' h
  | fail => rw [hm] at h; exact h
  | unsupported => trivial
  | outOfFuel => trivial

theorem outP_pureD {α : Type} {a : α} {st : WDSt} {P : α → WDSt → Prop} (h : P a st) :
    OutPD P ((pure a : WDM α) st) := h

theorem outP_unsupportedD {α : Type} {st : WDSt} {P : α → WDSt → Prop} : OutPD P ((wdUnsupported : WDM α) st) :=
  trivial

theorem outP_monoD {α : Type} {P Q : α → WDSt → Prop} {r : WDOut α} (h : OutPD P r)
    (hPQ : ∀ a st, P a st → Q a st) : OutPD Q r := by
  cases r with
  | ok a st => exact hPQ a st h
  | fail => exact h
  | unsupported => trivial
  | outOfFuel => trivial

theorem ne_fail_of_outPD {α : Type} {P : α → WDSt → Prop} {r : WDOut α} (h : OutPD P r) : r ≠ .fail := by
  intro e; subst e; exact h

theorem outP_okD {α : Type} {P : α → WDSt → Prop} {r : WDOut α} {a : α} {st : WDSt} (h : OutPD P r)
    (e : r = .ok a st) : P a st := by subst e; exact h

/-! ## L1: substitution on annotated phrases -/

theorem rsbList_nilD (s : RSub) : rsbList s [] = [] := rfl

mutual
theorem stripAtPat_sbD (s : RSub) : ∀ p : AAtPat, stripAtPat (rsbAtPat s p) = rsbAtPat s (stripAtPat p)
  | .wild _ | .scon _ _ | .var _ _ | .unit | .nil _ | .record _ _ => rfl
  | .con _ _ _ => rfl
  | .tuple p1 p2 p3 => by
    simp only [rsbAtPat, stripAtPat, stripPat_sbD s p1, stripPat_sbD s p2, stripPatOpt_sbD s p3]
  | .paren p => by simp only [rsbAtPat, stripAtPat, stripPat_sbD s p]
theorem stripPat_sbD (s : RSub) : ∀ p : APat, stripPat (rsbPat s p) = rsbPat s (stripPat p)
  | .atpat a => by simp only [rsbPat, stripPat, stripAtPat_sbD s a]
  | .con _ _ args _ => by simp only [rsbPat, stripPat, stripAtPats_sbD s args, rsbList_nilD]
  | .cons p1 p2 => by simp only [rsbPat, stripPat, stripPat_sbD s p1, stripPat_sbD s p2]
  | .as p _ => by simp only [rsbPat, stripPat, stripPat_sbD s p]
theorem stripPatOpt_sbD (s : RSub) : ∀ p : Option APat, stripPatOpt (rsbPatOpt s p) = rsbPatOpt s (stripPatOpt p)
  | none => rfl
  | some p => by simp only [rsbPatOpt, stripPatOpt, stripPat_sbD s p]
theorem stripAtPats_sbD (s : RSub) : ∀ l : List AAtPat, stripAtPats (rsbAtPats s l) = rsbAtPats s (stripAtPats l)
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, stripAtPats, stripAtPat_sbD s a, stripAtPats_sbD s as]
end

mutual
theorem stripAtExp_sbD (s : RSub) : ∀ a : AAtExp, stripAtExp (rsbAtExp s a) = rsbAtExp s (stripAtExp a)
  | .scon _ _ | .unit | .nil _ => rfl
  | .record r => by
    simp only [rsbAtExp, stripAtExp, stripExpRowOpt_sbD s r]
  | .var _ _ _ | .con _ _ _ | .op _ _ _ => rfl
  | .tuple e1 e2 e3 => by
    simp only [rsbAtExp, stripAtExp, stripExp_sbD s e1, stripExp_sbD s e2, stripExpOpt_sbD s e3]
  | .update _ _ _ r => by simp only [rsbAtExp, stripAtExp, stripExpRow_sbD s r, rsbList_nilD]
  | .letE d e => by simp only [rsbAtExp, stripAtExp, stripDec_sbD s d, stripExp_sbD s e]
  | .paren e => by simp only [rsbAtExp, stripAtExp, stripExp_sbD s e]
theorem stripExpRow_sbD (s : RSub) : ∀ r : AExpRow, stripExpRow (rsbExpRow s r) = rsbExpRow s (stripExpRow r)
  | .field _ e rest => by simp only [rsbExpRow, stripExpRow, stripExp_sbD s e, stripExpRowOpt_sbD s rest]
theorem stripExpRowOpt_sbD (s : RSub) : ∀ r : Option AExpRow,
    stripExpRowOpt (rsbExpRowOpt s r) = rsbExpRowOpt s (stripExpRowOpt r)
  | none => rfl
  | some r => by simp only [rsbExpRowOpt, stripExpRowOpt, stripExpRow_sbD s r]
theorem stripExp_sbD (s : RSub) : ∀ e : AExp, stripExp (rsbExp s e) = rsbExp s (stripExp e)
  | .atexp a => by simp only [rsbExp, stripExp, stripAtExp_sbD s a]
  | .app e a => by simp only [rsbExp, stripExp, stripExp_sbD s e, stripAtExp_sbD s a]
  | .lam p e => by simp only [rsbExp, stripExp, stripAtPat_sbD s p, stripExp_sbD s e]
  | .caseE e m => by simp only [rsbExp, stripExp, stripExp_sbD s e, stripMatch_sbD s m]
theorem stripExpOpt_sbD (s : RSub) : ∀ e : Option AExp, stripExpOpt (rsbExpOpt s e) = rsbExpOpt s (stripExpOpt e)
  | none => rfl
  | some e => by simp only [rsbExpOpt, stripExpOpt, stripExp_sbD s e]
theorem stripMatch_sbD (s : RSub) : ∀ m : AMatch, stripMatch (rsbMatch s m) = rsbMatch s (stripMatch m)
  | .mk mr rest => by simp only [rsbMatch, stripMatch, stripMRule_sbD s mr, stripMatchOpt_sbD s rest]
theorem stripMatchOpt_sbD (s : RSub) : ∀ m : Option AMatch,
    stripMatchOpt (rsbMatchOpt s m) = rsbMatchOpt s (stripMatchOpt m)
  | none => rfl
  | some m => by simp only [rsbMatchOpt, stripMatchOpt, stripMatch_sbD s m]
theorem stripMRule_sbD (s : RSub) : ∀ mr : AMRule, stripMRule (rsbMRule s mr) = rsbMRule s (stripMRule mr)
  | .mk p e => by simp only [rsbMRule, stripMRule, stripPat_sbD s p, stripExp_sbD s e]
theorem stripDec_sbD (s : RSub) : ∀ d : ADec, stripDec (rsbDec s d) = rsbDec s (stripDec d)
  | .val VE vb => by simp only [rsbDec, stripDec, stripValBind_sbD s vb]
theorem stripValBind_sbD (s : RSub) : ∀ vb : AValBind, stripValBind (rsbValBind s vb) = rsbValBind s (stripValBind vb)
  | .var _ _ _ e rest => by simp only [rsbValBind, stripValBind, stripExp_sbD s e, stripValBindOpt_sbD s rest]
  | .pat p e => by simp only [rsbValBind, stripValBind, stripAtPat_sbD s p, stripExp_sbD s e]
theorem stripValBindOpt_sbD (s : RSub) : ∀ vb : Option AValBind,
    stripValBindOpt (rsbValBindOpt s vb) = rsbValBindOpt s (stripValBindOpt vb)
  | none => rfl
  | some vb => by simp only [rsbValBindOpt, stripValBindOpt, stripValBind_sbD s vb]
end

/-! ### Composition -/

theorem rsbScheme_sbD (s t : RSub) (σ : Scheme) : rsbScheme t (rsbScheme s σ) = rsbScheme (rcomp t s) σ := by
  simp only [rsbScheme, rsb_rsb]

theorem rsbVE_sbD (s t : RSub) (VE : ValEnv) : rsbVE t (rsbVE s VE) = rsbVE (rcomp t s) VE := by
  simp only [rsbVE, List.map_map]; congr 1; funext p; simp [rsbScheme_sbD]

theorem rsbOpt_sbD (s t : RSub) : ∀ o : Option Ty, rsbOpt t (rsbOpt s o) = rsbOpt (rcomp t s) o
  | none => rfl
  | some τ => by simp [rsbOpt, rsb_rsb]

mutual
theorem rsbAtPat_sbD (s t : RSub) : ∀ p : AAtPat, rsbAtPat t (rsbAtPat s p) = rsbAtPat (rcomp t s) p
  | .wild _ | .scon _ _ | .var _ _ | .nil _ => by simp only [rsbAtPat, rsb_rsb]
  | .unit => rfl
  | .con _ _ _ => by simp only [rsbAtPat, rsb_rsb, rsbList_rsb]
  | .record r _ => by simp only [rsbAtPat, rsb_rsb, rsbPatRowOpt_sbD s t r]
  | .tuple p1 p2 p3 => by simp only [rsbAtPat, rsbPat_sbD s t p1, rsbPat_sbD s t p2, rsbPatOpt_sbD s t p3]
  | .paren p => by simp only [rsbAtPat, rsbPat_sbD s t p]
theorem rsbPatRow_sbD (s t : RSub) : ∀ r : APatRow, rsbPatRow t (rsbPatRow s r) = rsbPatRow (rcomp t s) r
  | .field _ _ rest => by simp only [rsbPatRow, rsb_rsb, rsbPatRowOpt_sbD s t rest]
theorem rsbPatRowOpt_sbD (s t : RSub) : ∀ r : Option APatRow, rsbPatRowOpt t (rsbPatRowOpt s r) = rsbPatRowOpt (rcomp t s) r
  | none => rfl
  | some r => by simp only [rsbPatRowOpt, rsbPatRow_sbD s t r]
theorem rsbPat_sbD (s t : RSub) : ∀ p : APat, rsbPat t (rsbPat s p) = rsbPat (rcomp t s) p
  | .atpat a => by simp only [rsbPat, rsbAtPat_sbD s t a]
  | .con _ _ args _ => by simp only [rsbPat, rsb_rsb, rsbList_rsb, rsbAtPats_sbD s t args]
  | .cons p1 p2 => by simp only [rsbPat, rsbPat_sbD s t p1, rsbPat_sbD s t p2]
  | .as p _ => by simp only [rsbPat, rsbPat_sbD s t p]
theorem rsbPatOpt_sbD (s t : RSub) : ∀ p : Option APat, rsbPatOpt t (rsbPatOpt s p) = rsbPatOpt (rcomp t s) p
  | none => rfl
  | some p => by simp only [rsbPatOpt, rsbPat_sbD s t p]
theorem rsbAtPats_sbD (s t : RSub) : ∀ l : List AAtPat, rsbAtPats t (rsbAtPats s l) = rsbAtPats (rcomp t s) l
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, rsbAtPat_sbD s t a, rsbAtPats_sbD s t as]
end

mutual
theorem rsbAtExp_sbD (s t : RSub) : ∀ a : AAtExp, rsbAtExp t (rsbAtExp s a) = rsbAtExp (rcomp t s) a
  | .scon _ _ | .nil _ => by simp only [rsbAtExp, rsb_rsb]
  | .unit => rfl
  | .var _ _ _ | .con _ _ _ | .op _ _ _ => by simp only [rsbAtExp, rsb_rsb, rsbList_rsb]
  | .record r => by simp only [rsbAtExp, rsbExpRowOpt_sbD s t r]
  | .update _ _ _ r => by simp only [rsbAtExp, rsb_rsb, rsbList_rsb, rsbExpRow_sbD s t r]
  | .tuple e1 e2 e3 => by simp only [rsbAtExp, rsbExp_sbD s t e1, rsbExp_sbD s t e2, rsbExpOpt_sbD s t e3]
  | .letE d e => by simp only [rsbAtExp, rsbDec_sbD s t d, rsbExp_sbD s t e]
  | .paren e => by simp only [rsbAtExp, rsbExp_sbD s t e]
theorem rsbExpRow_sbD (s t : RSub) : ∀ r : AExpRow, rsbExpRow t (rsbExpRow s r) = rsbExpRow (rcomp t s) r
  | .field _ e rest => by simp only [rsbExpRow, rsbExp_sbD s t e, rsbExpRowOpt_sbD s t rest]
theorem rsbExpRowOpt_sbD (s t : RSub) : ∀ r : Option AExpRow, rsbExpRowOpt t (rsbExpRowOpt s r) = rsbExpRowOpt (rcomp t s) r
  | none => rfl
  | some r => by simp only [rsbExpRowOpt, rsbExpRow_sbD s t r]
theorem rsbExp_sbD (s t : RSub) : ∀ e : AExp, rsbExp t (rsbExp s e) = rsbExp (rcomp t s) e
  | .atexp a => by simp only [rsbExp, rsbAtExp_sbD s t a]
  | .app e a => by simp only [rsbExp, rsbExp_sbD s t e, rsbAtExp_sbD s t a]
  | .lam p e => by simp only [rsbExp, rsbAtPat_sbD s t p, rsbExp_sbD s t e]
  | .caseE e m => by simp only [rsbExp, rsbExp_sbD s t e, rsbMatch_sbD s t m]
theorem rsbExpOpt_sbD (s t : RSub) : ∀ e : Option AExp, rsbExpOpt t (rsbExpOpt s e) = rsbExpOpt (rcomp t s) e
  | none => rfl
  | some e => by simp only [rsbExpOpt, rsbExp_sbD s t e]
theorem rsbMatch_sbD (s t : RSub) : ∀ m : AMatch, rsbMatch t (rsbMatch s m) = rsbMatch (rcomp t s) m
  | .mk mr rest => by simp only [rsbMatch, rsbMRule_sbD s t mr, rsbMatchOpt_sbD s t rest]
theorem rsbMatchOpt_sbD (s t : RSub) : ∀ m : Option AMatch, rsbMatchOpt t (rsbMatchOpt s m) = rsbMatchOpt (rcomp t s) m
  | none => rfl
  | some m => by simp only [rsbMatchOpt, rsbMatch_sbD s t m]
theorem rsbMRule_sbD (s t : RSub) : ∀ mr : AMRule, rsbMRule t (rsbMRule s mr) = rsbMRule (rcomp t s) mr
  | .mk p e => by simp only [rsbMRule, rsbPat_sbD s t p, rsbExp_sbD s t e]
theorem rsbDec_sbD (s t : RSub) : ∀ d : ADec, rsbDec t (rsbDec s d) = rsbDec (rcomp t s) d
  | .val VE vb => by simp only [rsbDec, rsbVE_sbD, rsbValBind_sbD s t vb]
theorem rsbValBind_sbD (s t : RSub) : ∀ vb : AValBind, rsbValBind t (rsbValBind s vb) = rsbValBind (rcomp t s) vb
  | .var _ _ _ e rest => by simp only [rsbValBind, rsb_rsb, rsbExp_sbD s t e, rsbValBindOpt_sbD s t rest]
  | .pat p e => by simp only [rsbValBind, rsbAtPat_sbD s t p, rsbExp_sbD s t e]
theorem rsbValBindOpt_sbD (s t : RSub) : ∀ vb : Option AValBind, rsbValBindOpt t (rsbValBindOpt s vb) = rsbValBindOpt (rcomp t s) vb
  | none => rfl
  | some vb => by simp only [rsbValBindOpt, rsbValBind_sbD s t vb]
end

/-- A substitution that absorbs `θ` composes with it to itself. -/
theorem comp_of_absorbsD {s : RSub} {θ : RBnd} (h : AbsR s θ) : rcomp s (toRS θ) = s := absR_iff.mp h

theorem absorbs_compD {s : RSub} {θ : RBnd} (h : AbsR s θ) (τ : Ty) : rsb s (rsb (toRS θ) τ) = rsb s τ :=
  absR_rsb h τ

/-! ### Types and value environments of substituted phrases -/

theorem tupleTy_sbD (s : RSub) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    rsb s (tupleTy τ1 τ2 τ3) = tupleTy (rsb s τ1) (rsb s τ2) (rsbOpt s τ3) := by
  cases τ3 <;> rfl

theorem listTy_sbD (s : RSub) (τ : Ty) : rsb s (listTy τ) = listTy (rsb s τ) := rfl

theorem arrows_sbD (s : RSub) : ∀ (as : List Ty) (τ : Ty), rsb s (arrows as τ) = arrows (rsbList s as) (rsb s τ)
  | [], _ => rfl
  | a :: as, τ => by simp only [arrows, rsb, rsbList, arrows_sbD s as τ]

theorem cod_sbD (s : RSub) (τ1 τ2 : Ty) : rsb s (Ty.fn τ1 τ2).cod = (rsb s (Ty.fn τ1 τ2)).cod := rfl

mutual
theorem rsbAtPat_tyD (s : RSub) : ∀ p : AAtPat, (rsbAtPat s p).ty = rsb s p.ty
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .record _ _ => rfl
  | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [rsbAtPat, AAtPat.ty, rsbPat_tyD s p1, rsbPat_tyD s p2, rsbPatOpt_tyD s p3, tupleTy_sbD]
  | .paren p => by simp only [rsbAtPat, AAtPat.ty, rsbPat_tyD s p]
theorem rsbPat_tyD (s : RSub) : ∀ p : APat, (rsbPat s p).ty = rsb s p.ty
  | .atpat a => by simp only [rsbPat, APat.ty, rsbAtPat_tyD s a]
  | .con _ _ _ _ => rfl
  | .cons p1 _ => by simp only [rsbPat, APat.ty, rsbPat_tyD s p1, listTy_sbD]
  | .as p _ => by simp only [rsbPat, APat.ty, rsbPat_tyD s p]
theorem rsbPatOpt_tyD (s : RSub) : ∀ p : Option APat, APat.tyOpt (rsbPatOpt s p) = rsbOpt s (APat.tyOpt p)
  | none => rfl
  | some p => by simp only [rsbPatOpt, APat.tyOpt, rsbPat_tyD s p, rsbOpt]
end

theorem rsbAtPats_tyListD (s : RSub) : ∀ l : List AAtPat, AAtPat.tyList (rsbAtPats s l) = rsbList s (AAtPat.tyList l)
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, AAtPat.tyList, rsbAtPat_tyD s a, rsbAtPats_tyListD s as, rsbList]

theorem rsbVE_filterD (s : RSub) (ks : List String) : ∀ f : ValEnv,
    rsbVE s (f.filter fun p => !decide (p.1 ∈ ks)) = (rsbVE s f).filter fun p => !decide (p.1 ∈ ks)
  | [] => rfl
  | p :: r => by
    have ih := rsbVE_filterD s ks r
    simp only [rsbVE] at ih
    by_cases h : p.1 ∈ ks <;> simp [List.filter_cons, rsbVE, h, ih]

theorem rsbVE_keysD (s : RSub) (f : ValEnv) : FMap.keys (rsbVE s f) = FMap.keys f := by
  simp [rsbVE, FMap.keys]

theorem rsbVE_modifyD (s : RSub) (f g : ValEnv) : rsbVE s (FMap.modify f g) = FMap.modify (rsbVE s f) (rsbVE s g) := by
  simp only [FMap.modify]
  rw [show rsbVE s (g ++ _) = rsbVE s g ++ rsbVE s _ from List.map_append, rsbVE_filterD, rsbVE_keysD]

theorem rsbVE_nilD (s : RSub) : rsbVE s [] = [] := rfl

theorem rsbVE_plusAllD (s : RSub) (l : List ValEnv) : rsbVE s (FMap.plusAll l) = FMap.plusAll (l.map (rsbVE s)) := by
  unfold FMap.plusAll
  suffices h : ∀ acc, rsbVE s (l.foldl FMap.modify acc) = (l.map (rsbVE s)).foldl FMap.modify (rsbVE s acc) from h []
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; simp only [List.foldl_cons, List.map_cons]; rw [ih, rsbVE_modifyD]

theorem rsbScheme_monoD (s : RSub) (τ : Ty) : rsbScheme s (mono τ) = mono (rsb s τ) := rfl

mutual
theorem rsbAtPat_veD (s : RSub) : ∀ p : AAtPat, (rsbAtPat s p).ve = rsbVE s p.ve
  | .wild _ | .scon _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .var _ _ => rfl
  | .record r _ => by simp only [rsbAtPat, AAtPat.ve, rsbPatRowOpt_veD s r]
  | .tuple p1 p2 p3 => by
    simp only [rsbAtPat, AAtPat.ve, rsbPat_veD s p1, rsbPat_veD s p2, rsbPatOpt_veD s p3, rsbVE_modifyD]
  | .paren p => by simp only [rsbAtPat, AAtPat.ve, rsbPat_veD s p]
theorem rsbPatRow_veD (s : RSub) : ∀ r : APatRow, (rsbPatRow s r).ve = rsbVE s r.ve
  | .field _ _ rest => by simp only [rsbPatRow, APatRow.ve, rsbPatRowOpt_veD s rest, rsbVE_modifyD]; rfl
theorem rsbPatRowOpt_veD (s : RSub) : ∀ r : Option APatRow, APatRow.veOpt (rsbPatRowOpt s r) = rsbVE s (APatRow.veOpt r)
  | none => rfl
  | some r => by simp only [rsbPatRowOpt, APatRow.veOpt, rsbPatRow_veD s r]
theorem rsbPat_veD (s : RSub) : ∀ p : APat, (rsbPat s p).ve = rsbVE s p.ve
  | .atpat a => by simp only [rsbPat, APat.ve, rsbAtPat_veD s a]
  | .con _ _ args _ => by simp only [rsbPat, APat.ve, rsbAtPats_veListD s args, rsbVE_plusAllD]
  | .cons p1 p2 => by simp only [rsbPat, APat.ve, rsbPat_veD s p1, rsbPat_veD s p2, rsbVE_modifyD]
  | .as p _ => by simp only [rsbPat, APat.ve, rsbPat_veD s p, rsbVE_modifyD, rsbPat_tyD s p]; rfl
theorem rsbPatOpt_veD (s : RSub) : ∀ p : Option APat, APat.veOpt (rsbPatOpt s p) = rsbVE s (APat.veOpt p)
  | none => rfl
  | some p => by simp only [rsbPatOpt, APat.veOpt, rsbPat_veD s p]
theorem rsbAtPats_veListD (s : RSub) : ∀ l : List AAtPat, AAtPat.veList (rsbAtPats s l) = (AAtPat.veList l).map (rsbVE s)
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, AAtPat.veList, rsbAtPat_veD s a, rsbAtPats_veListD s as, List.map_cons]
end

theorem rsbRow_modifyFD (s : RSub) : ∀ (f : Nat) (ρ ρ' : Row),
    rsbRow s (Row.modifyF f ρ ρ') = Row.modifyF f (rsbRow s ρ) (rsbRow s ρ')
  | _, [], _ => by simp only [Row.modifyF, rsbRow]
  | _, _ :: _, [] => by simp only [Row.modifyF, rsbRow]
  | 0, _ :: _, _ :: _ => by simp only [Row.modifyF, rsbRow_eq, mapV, List.map_append, List.map_cons]
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [Row.modifyF, rsbRow]
    split
    · simp only [rsbRow, rsbRow_modifyFD s f r1 r2]
    · split
      · simp only [rsbRow, rsbRow_modifyFD s f r1 ((l2, τ2) :: r2)]
      · simp only [rsbRow, rsbRow_modifyFD s f ((l1, τ1) :: r1) r2]

theorem rsbRow_lengthD (s : RSub) (ρ : Row) : (rsbRow s ρ).length = ρ.length := by
  rw [rsbRow_eq]; simp [mapV]

theorem rsbRow_modifyD (s : RSub) (ρ ρ' : Row) : rsbRow s (Row.modify ρ ρ') = Row.modify (rsbRow s ρ) (rsbRow s ρ') := by
  simp only [Row.modify, rsbRow_modifyFD, rsbRow_lengthD]

end StandardElm.Stat.Complete
