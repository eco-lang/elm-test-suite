/-
  A Standard Definition of Elm? Mechanisation: basic lemmas for the proof of completeness and
  principality of W (plan step 11, milestone (b), section 8: L1, the substitution algebra on
  annotated phrases), and the outcome predicate of a run of W.

  * Variables: `isNew n a` (a variable W creates at or above the counter `n`), `isBndT`, and
    `OkT n τ`: the variables of `τ` are type variables, not `bnd`, below `n` (every type W builds
    in F_b is of this form).
  * L1: substitution commutes with erasure, with the instance lists left out (`stripExp`), with
    the type and the value environment an annotated phrase determines, and composes.
  * `OutP P r`: the outcome `r` of W is not `fail`, and if it is `ok` it satisfies `P`.
-/
import StandardElmMech.Stat.Complete.WPrincipal

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Variables -/

/-! `TyVar.isNew n`: a variable W creates when its counter is at least `n` (MguC.lean). -/

def _root_.StandardElm.Stat.TyVar.isBndT : TyVar → Bool
  | .bnd _ _ => true
  | _ => false

theorem rigidFrom_eq (n0 : Nat) (a : TyVar) : rigidFrom n0 a = !a.isNew n0 := by
  cases a with
  | fresh k c => simp only [rigidFrom, TyVar.isNew]; by_cases h : k < n0 <;> simp [h] <;> omega
  | _ => rfl

theorem rigid_of_old {n0 : Nat} {a : TyVar} (h : a.isNew n0 = false) : rigidFrom n0 a = true := by
  rw [rigidFrom_eq, h]; rfl

theorem not_rigid_of_new {n0 n : Nat} (h0 : n0 ≤ n) {a : TyVar} (h : a.isNew n = true) :
    rigidFrom n0 a = false := by
  rw [rigidFrom_eq]
  cases a <;> simp_all [TyVar.isNew]; omega

theorem isNew_fresh (n : Nat) {c : Cls} : (TyVar.fresh n c).isNew n = true := by simp [TyVar.isNew]

theorem isNew_fresh_lt {n m : Nat} {c : Cls} (h : n < m) : (TyVar.fresh n c).isNew m = false := by
  simp [TyVar.isNew]; omega

/-- A type W builds: its variables are type variables, not `bnd`, below the counter. -/
def OkT (n : Nat) (τ : Ty) : Prop :=
  ∀ v ∈ τ.vars, ∃ a, v = .ty a ∧ a.isBndT = false ∧ a.isNew n = false

theorem OkT.mono {n m : Nat} (h : n ≤ m) {τ : Ty} (hτ : OkT n τ) : OkT m τ := fun v hv => by
  obtain ⟨a, rfl, h1, h2⟩ := hτ v hv; exact ⟨a, rfl, h1, isNew_mono h h2⟩

theorem OkT_var {n : Nat} {a : TyVar} (h1 : a.isBndT = false) (h2 : a.isNew n = false) : OkT n (.var a) := by
  intro v hv; simp only [Ty.vars, List.mem_singleton] at hv; exact ⟨a, hv, h1, h2⟩

theorem OkT_con {n : Nat} {t : TyName} : ∀ {as : List Ty}, (∀ τ ∈ as, OkT n τ) → OkT n (.con as t)
  | [], _ => by intro v hv; simp [Ty.vars, Ty.listVars] at hv
  | τ :: as, h => by
    intro v hv
    simp only [Ty.vars, Ty.listVars, List.mem_append] at hv
    rcases hv with hv | hv
    · exact h τ (.head _) v hv
    · exact OkT_con (t := t) (fun x hx => h x (.tail _ hx)) v (by simpa [Ty.vars] using hv)

theorem OkT_fn {n : Nat} {a b : Ty} (ha : OkT n a) (hb : OkT n b) : OkT n (.fn a b) := by
  intro v hv; simp only [Ty.vars, List.mem_append] at hv
  rcases hv with hv | hv
  · exact ha v hv
  · exact hb v hv

theorem OkT_fn_iff {n : Nat} {a b : Ty} : OkT n (.fn a b) ↔ OkT n a ∧ OkT n b :=
  ⟨fun h => ⟨fun v hv => h v (by simp [Ty.vars, hv]), fun v hv => h v (by simp [Ty.vars, hv])⟩,
   fun ⟨ha, hb⟩ => OkT_fn ha hb⟩

theorem OkT_of_vars_nil {n : Nat} {τ : Ty} (h : τ.vars = []) : OkT n τ := by
  intro v hv; rw [h] at hv; cases hv

theorem OkT_list {n : Nat} {τ : Ty} (h : OkT n τ) : OkT n (listTy τ) :=
  OkT_con (fun x hx => by simp at hx; subst hx; exact h)

theorem OkT_tuple {n : Nat} {τ1 τ2 : Ty} {τ3 : Option Ty} (h1 : OkT n τ1) (h2 : OkT n τ2)
    (h3 : ∀ τ, τ3 = some τ → OkT n τ) : OkT n (tupleTy τ1 τ2 τ3) := by
  cases τ3 with
  | none => exact OkT_con (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption)
  | some τ =>
    exact OkT_con (fun x hx => by
      simp at hx; rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3 _ rfl)

/-- The image of an `OkT` type under a substitution whose images of its variables are `OkT`. -/
theorem OkT_sb {n : Nat} {s : FSub} {τ : Ty} (hτ : OkT n τ) (hs : ∀ a, BVar.ty a ∈ τ.vars → OkT n (s a)) :
    OkT n (sb s τ) := by
  intro v hv
  rcases vars_sb s τ v hv with ⟨e, rfl, he⟩ | ⟨a, ha, hv'⟩
  · obtain ⟨_, h, _⟩ := hτ _ he; cases h
  · exact hs a ha v hv'

/-! ## The outcome of a run -/

/-- The outcome is not a failure, and an `ok` outcome satisfies `P`. -/
def OutP {α : Type} (P : α → WSt → Prop) : WOut α → Prop
  | .ok a st => P a st
  | .fail => False
  | .unsupported => True
  | .outOfFuel => True

theorem outP_bind {α β : Type} {m : WM α} {f : α → WM β} {st : WSt} {Q : α → WSt → Prop}
    {P : β → WSt → Prop} (h : OutP Q (m st)) (hf : ∀ a st', Q a st' → OutP P (f a st')) :
    OutP P ((m >>= f) st) := by
  show OutP P (WM.bind m f st)
  unfold WM.bind
  cases hm : m st with
  | ok a st' => rw [hm] at h; exact hf a st' h
  | fail => rw [hm] at h; exact h
  | unsupported => trivial
  | outOfFuel => trivial

theorem outP_pure {α : Type} {a : α} {st : WSt} {P : α → WSt → Prop} (h : P a st) :
    OutP P ((pure a : WM α) st) := h

theorem outP_unsupported {α : Type} {st : WSt} {P : α → WSt → Prop} : OutP P ((wUnsupported : WM α) st) :=
  trivial

theorem outP_mono {α : Type} {P Q : α → WSt → Prop} {r : WOut α} (h : OutP P r)
    (hPQ : ∀ a st, P a st → Q a st) : OutP Q r := by
  cases r with
  | ok a st => exact hPQ a st h
  | fail => exact h
  | unsupported => trivial
  | outOfFuel => trivial

theorem ne_fail_of_outP {α : Type} {P : α → WSt → Prop} {r : WOut α} (h : OutP P r) : r ≠ .fail := by
  intro e; subst e; exact h

theorem outP_ok {α : Type} {P : α → WSt → Prop} {r : WOut α} {a : α} {st : WSt} (h : OutP P r)
    (e : r = .ok a st) : P a st := by subst e; exact h

/-! ## L1: substitution on annotated phrases -/

theorem sbList_nil (s : FSub) : sbList s [] = [] := rfl

mutual
theorem stripAtPat_sb (s : FSub) : ∀ p : AAtPat, stripAtPat (sbAtPat s p) = sbAtPat s (stripAtPat p)
  | .wild _ | .scon _ _ | .var _ _ | .unit | .nil _ | .record _ _ => rfl
  | .con _ _ _ => rfl
  | .tuple p1 p2 p3 => by
    simp only [sbAtPat, stripAtPat, stripPat_sb s p1, stripPat_sb s p2, stripPatOpt_sb s p3]
  | .paren p => by simp only [sbAtPat, stripAtPat, stripPat_sb s p]
theorem stripPat_sb (s : FSub) : ∀ p : APat, stripPat (sbPat s p) = sbPat s (stripPat p)
  | .atpat a => by simp only [sbPat, stripPat, stripAtPat_sb s a]
  | .con _ _ args _ => by simp only [sbPat, stripPat, stripAtPats_sb s args, sbList_nil]
  | .cons p1 p2 => by simp only [sbPat, stripPat, stripPat_sb s p1, stripPat_sb s p2]
  | .as p _ => by simp only [sbPat, stripPat, stripPat_sb s p]
theorem stripPatOpt_sb (s : FSub) : ∀ p : Option APat, stripPatOpt (sbPatOpt s p) = sbPatOpt s (stripPatOpt p)
  | none => rfl
  | some p => by simp only [sbPatOpt, stripPatOpt, stripPat_sb s p]
theorem stripAtPats_sb (s : FSub) : ∀ l : List AAtPat, stripAtPats (sbAtPats s l) = sbAtPats s (stripAtPats l)
  | [] => rfl
  | a :: as => by simp only [sbAtPats, stripAtPats, stripAtPat_sb s a, stripAtPats_sb s as]
end

mutual
theorem stripAtExp_sb (s : FSub) : ∀ a : AAtExp, stripAtExp (sbAtExp s a) = sbAtExp s (stripAtExp a)
  | .scon _ _ | .unit | .nil _ => rfl
  | .record r => by
    simp only [sbAtExp, stripAtExp, stripExpRowOpt_sb s r]
  | .var _ _ _ | .con _ _ _ | .op _ _ _ => rfl
  | .tuple e1 e2 e3 => by
    simp only [sbAtExp, stripAtExp, stripExp_sb s e1, stripExp_sb s e2, stripExpOpt_sb s e3]
  | .update _ _ _ r => by simp only [sbAtExp, stripAtExp, stripExpRow_sb s r, sbList_nil]
  | .letE d e => by simp only [sbAtExp, stripAtExp, stripDec_sb s d, stripExp_sb s e]
  | .paren e => by simp only [sbAtExp, stripAtExp, stripExp_sb s e]
theorem stripExpRow_sb (s : FSub) : ∀ r : AExpRow, stripExpRow (sbExpRow s r) = sbExpRow s (stripExpRow r)
  | .field _ e rest => by simp only [sbExpRow, stripExpRow, stripExp_sb s e, stripExpRowOpt_sb s rest]
theorem stripExpRowOpt_sb (s : FSub) : ∀ r : Option AExpRow,
    stripExpRowOpt (sbExpRowOpt s r) = sbExpRowOpt s (stripExpRowOpt r)
  | none => rfl
  | some r => by simp only [sbExpRowOpt, stripExpRowOpt, stripExpRow_sb s r]
theorem stripExp_sb (s : FSub) : ∀ e : AExp, stripExp (sbExp s e) = sbExp s (stripExp e)
  | .atexp a => by simp only [sbExp, stripExp, stripAtExp_sb s a]
  | .app e a => by simp only [sbExp, stripExp, stripExp_sb s e, stripAtExp_sb s a]
  | .lam p e => by simp only [sbExp, stripExp, stripAtPat_sb s p, stripExp_sb s e]
  | .caseE e m => by simp only [sbExp, stripExp, stripExp_sb s e, stripMatch_sb s m]
theorem stripExpOpt_sb (s : FSub) : ∀ e : Option AExp, stripExpOpt (sbExpOpt s e) = sbExpOpt s (stripExpOpt e)
  | none => rfl
  | some e => by simp only [sbExpOpt, stripExpOpt, stripExp_sb s e]
theorem stripMatch_sb (s : FSub) : ∀ m : AMatch, stripMatch (sbMatch s m) = sbMatch s (stripMatch m)
  | .mk mr rest => by simp only [sbMatch, stripMatch, stripMRule_sb s mr, stripMatchOpt_sb s rest]
theorem stripMatchOpt_sb (s : FSub) : ∀ m : Option AMatch,
    stripMatchOpt (sbMatchOpt s m) = sbMatchOpt s (stripMatchOpt m)
  | none => rfl
  | some m => by simp only [sbMatchOpt, stripMatchOpt, stripMatch_sb s m]
theorem stripMRule_sb (s : FSub) : ∀ mr : AMRule, stripMRule (sbMRule s mr) = sbMRule s (stripMRule mr)
  | .mk p e => by simp only [sbMRule, stripMRule, stripPat_sb s p, stripExp_sb s e]
theorem stripDec_sb (s : FSub) : ∀ d : ADec, stripDec (sbDec s d) = sbDec s (stripDec d)
  | .val VE vb => by simp only [sbDec, stripDec, stripValBind_sb s vb]
theorem stripValBind_sb (s : FSub) : ∀ vb : AValBind, stripValBind (sbValBind s vb) = sbValBind s (stripValBind vb)
  | .var _ _ _ e rest => by simp only [sbValBind, stripValBind, stripExp_sb s e, stripValBindOpt_sb s rest]
  | .pat p e => by simp only [sbValBind, stripValBind, stripAtPat_sb s p, stripExp_sb s e]
theorem stripValBindOpt_sb (s : FSub) : ∀ vb : Option AValBind,
    stripValBindOpt (sbValBindOpt s vb) = sbValBindOpt s (stripValBindOpt vb)
  | none => rfl
  | some vb => by simp only [sbValBindOpt, stripValBindOpt, stripValBind_sb s vb]
end

/-! ### Composition -/

theorem sbScheme_sb (s t : FSub) (σ : Scheme) : sbScheme t (sbScheme s σ) = sbScheme (comp t s) σ := by
  simp only [sbScheme, sb_sb]

theorem sbVE_sb (s t : FSub) (VE : ValEnv) : sbVE t (sbVE s VE) = sbVE (comp t s) VE := by
  simp only [sbVE, List.map_map]; congr 1; funext p; simp [sbScheme_sb]

theorem sbOpt_sb (s t : FSub) : ∀ o : Option Ty, sbOpt t (sbOpt s o) = sbOpt (comp t s) o
  | none => rfl
  | some τ => by simp [sbOpt, sb_sb]

mutual
theorem sbAtPat_sb (s t : FSub) : ∀ p : AAtPat, sbAtPat t (sbAtPat s p) = sbAtPat (comp t s) p
  | .wild _ | .scon _ _ | .var _ _ | .nil _ => by simp only [sbAtPat, sb_sb]
  | .unit => rfl
  | .con _ _ _ => by simp only [sbAtPat, sb_sb, sbList_sb]
  | .record r _ => by simp only [sbAtPat, sb_sb, sbPatRowOpt_sb s t r]
  | .tuple p1 p2 p3 => by simp only [sbAtPat, sbPat_sb s t p1, sbPat_sb s t p2, sbPatOpt_sb s t p3]
  | .paren p => by simp only [sbAtPat, sbPat_sb s t p]
theorem sbPatRow_sb (s t : FSub) : ∀ r : APatRow, sbPatRow t (sbPatRow s r) = sbPatRow (comp t s) r
  | .field _ _ rest => by simp only [sbPatRow, sb_sb, sbPatRowOpt_sb s t rest]
theorem sbPatRowOpt_sb (s t : FSub) : ∀ r : Option APatRow, sbPatRowOpt t (sbPatRowOpt s r) = sbPatRowOpt (comp t s) r
  | none => rfl
  | some r => by simp only [sbPatRowOpt, sbPatRow_sb s t r]
theorem sbPat_sb (s t : FSub) : ∀ p : APat, sbPat t (sbPat s p) = sbPat (comp t s) p
  | .atpat a => by simp only [sbPat, sbAtPat_sb s t a]
  | .con _ _ args _ => by simp only [sbPat, sb_sb, sbList_sb, sbAtPats_sb s t args]
  | .cons p1 p2 => by simp only [sbPat, sbPat_sb s t p1, sbPat_sb s t p2]
  | .as p _ => by simp only [sbPat, sbPat_sb s t p]
theorem sbPatOpt_sb (s t : FSub) : ∀ p : Option APat, sbPatOpt t (sbPatOpt s p) = sbPatOpt (comp t s) p
  | none => rfl
  | some p => by simp only [sbPatOpt, sbPat_sb s t p]
theorem sbAtPats_sb (s t : FSub) : ∀ l : List AAtPat, sbAtPats t (sbAtPats s l) = sbAtPats (comp t s) l
  | [] => rfl
  | a :: as => by simp only [sbAtPats, sbAtPat_sb s t a, sbAtPats_sb s t as]
end

mutual
theorem sbAtExp_sb (s t : FSub) : ∀ a : AAtExp, sbAtExp t (sbAtExp s a) = sbAtExp (comp t s) a
  | .scon _ _ | .nil _ => by simp only [sbAtExp, sb_sb]
  | .unit => rfl
  | .var _ _ _ | .con _ _ _ | .op _ _ _ => by simp only [sbAtExp, sb_sb, sbList_sb]
  | .record r => by simp only [sbAtExp, sbExpRowOpt_sb s t r]
  | .update _ _ _ r => by simp only [sbAtExp, sb_sb, sbList_sb, sbExpRow_sb s t r]
  | .tuple e1 e2 e3 => by simp only [sbAtExp, sbExp_sb s t e1, sbExp_sb s t e2, sbExpOpt_sb s t e3]
  | .letE d e => by simp only [sbAtExp, sbDec_sb s t d, sbExp_sb s t e]
  | .paren e => by simp only [sbAtExp, sbExp_sb s t e]
theorem sbExpRow_sb (s t : FSub) : ∀ r : AExpRow, sbExpRow t (sbExpRow s r) = sbExpRow (comp t s) r
  | .field _ e rest => by simp only [sbExpRow, sbExp_sb s t e, sbExpRowOpt_sb s t rest]
theorem sbExpRowOpt_sb (s t : FSub) : ∀ r : Option AExpRow, sbExpRowOpt t (sbExpRowOpt s r) = sbExpRowOpt (comp t s) r
  | none => rfl
  | some r => by simp only [sbExpRowOpt, sbExpRow_sb s t r]
theorem sbExp_sb (s t : FSub) : ∀ e : AExp, sbExp t (sbExp s e) = sbExp (comp t s) e
  | .atexp a => by simp only [sbExp, sbAtExp_sb s t a]
  | .app e a => by simp only [sbExp, sbExp_sb s t e, sbAtExp_sb s t a]
  | .lam p e => by simp only [sbExp, sbAtPat_sb s t p, sbExp_sb s t e]
  | .caseE e m => by simp only [sbExp, sbExp_sb s t e, sbMatch_sb s t m]
theorem sbExpOpt_sb (s t : FSub) : ∀ e : Option AExp, sbExpOpt t (sbExpOpt s e) = sbExpOpt (comp t s) e
  | none => rfl
  | some e => by simp only [sbExpOpt, sbExp_sb s t e]
theorem sbMatch_sb (s t : FSub) : ∀ m : AMatch, sbMatch t (sbMatch s m) = sbMatch (comp t s) m
  | .mk mr rest => by simp only [sbMatch, sbMRule_sb s t mr, sbMatchOpt_sb s t rest]
theorem sbMatchOpt_sb (s t : FSub) : ∀ m : Option AMatch, sbMatchOpt t (sbMatchOpt s m) = sbMatchOpt (comp t s) m
  | none => rfl
  | some m => by simp only [sbMatchOpt, sbMatch_sb s t m]
theorem sbMRule_sb (s t : FSub) : ∀ mr : AMRule, sbMRule t (sbMRule s mr) = sbMRule (comp t s) mr
  | .mk p e => by simp only [sbMRule, sbPat_sb s t p, sbExp_sb s t e]
theorem sbDec_sb (s t : FSub) : ∀ d : ADec, sbDec t (sbDec s d) = sbDec (comp t s) d
  | .val VE vb => by simp only [sbDec, sbVE_sb, sbValBind_sb s t vb]
theorem sbValBind_sb (s t : FSub) : ∀ vb : AValBind, sbValBind t (sbValBind s vb) = sbValBind (comp t s) vb
  | .var _ _ _ e rest => by simp only [sbValBind, sb_sb, sbExp_sb s t e, sbValBindOpt_sb s t rest]
  | .pat p e => by simp only [sbValBind, sbAtPat_sb s t p, sbExp_sb s t e]
theorem sbValBindOpt_sb (s t : FSub) : ∀ vb : Option AValBind, sbValBindOpt t (sbValBindOpt s vb) = sbValBindOpt (comp t s) vb
  | none => rfl
  | some vb => by simp only [sbValBindOpt, sbValBind_sb s t vb]
end

/-- A substitution that absorbs `θ` composes with it to itself. -/
theorem comp_of_absorbs {s θ : FSub} (h : Absorbs s θ) : comp s θ = s := by
  funext a; exact h a

theorem absorbs_comp {s θ : FSub} (h : Absorbs s θ) (τ : Ty) : sb s (sb θ τ) = sb s τ := by
  rw [sb_sb, comp_of_absorbs h]

/-! ### Types and value environments of substituted phrases -/

theorem tupleTy_sb (s : FSub) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    sb s (tupleTy τ1 τ2 τ3) = tupleTy (sb s τ1) (sb s τ2) (sbOpt s τ3) := by
  cases τ3 <;> rfl

theorem listTy_sb (s : FSub) (τ : Ty) : sb s (listTy τ) = listTy (sb s τ) := rfl

theorem arrows_sb (s : FSub) : ∀ (as : List Ty) (τ : Ty), sb s (arrows as τ) = arrows (sbList s as) (sb s τ)
  | [], _ => rfl
  | a :: as, τ => by simp only [arrows, sb, sbList, arrows_sb s as τ]

theorem cod_sb (s : FSub) (τ1 τ2 : Ty) : sb s (Ty.fn τ1 τ2).cod = (sb s (Ty.fn τ1 τ2)).cod := rfl

mutual
theorem sbAtPat_ty (s : FSub) : ∀ p : AAtPat, (sbAtPat s p).ty = sb s p.ty
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .record _ _ => rfl
  | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [sbAtPat, AAtPat.ty, sbPat_ty s p1, sbPat_ty s p2, sbPatOpt_ty s p3, tupleTy_sb]
  | .paren p => by simp only [sbAtPat, AAtPat.ty, sbPat_ty s p]
theorem sbPat_ty (s : FSub) : ∀ p : APat, (sbPat s p).ty = sb s p.ty
  | .atpat a => by simp only [sbPat, APat.ty, sbAtPat_ty s a]
  | .con _ _ _ _ => rfl
  | .cons p1 _ => by simp only [sbPat, APat.ty, sbPat_ty s p1, listTy_sb]
  | .as p _ => by simp only [sbPat, APat.ty, sbPat_ty s p]
theorem sbPatOpt_ty (s : FSub) : ∀ p : Option APat, APat.tyOpt (sbPatOpt s p) = sbOpt s (APat.tyOpt p)
  | none => rfl
  | some p => by simp only [sbPatOpt, APat.tyOpt, sbPat_ty s p, sbOpt]
end

theorem sbAtPats_tyList (s : FSub) : ∀ l : List AAtPat, AAtPat.tyList (sbAtPats s l) = sbList s (AAtPat.tyList l)
  | [] => rfl
  | a :: as => by simp only [sbAtPats, AAtPat.tyList, sbAtPat_ty s a, sbAtPats_tyList s as, sbList]

theorem sbVE_filter (s : FSub) (ks : List String) : ∀ f : ValEnv,
    sbVE s (f.filter fun p => !decide (p.1 ∈ ks)) = (sbVE s f).filter fun p => !decide (p.1 ∈ ks)
  | [] => rfl
  | p :: r => by
    have ih := sbVE_filter s ks r
    simp only [sbVE] at ih
    by_cases h : p.1 ∈ ks <;> simp [List.filter_cons, sbVE, h, ih]

theorem sbVE_keys (s : FSub) (f : ValEnv) : FMap.keys (sbVE s f) = FMap.keys f := by
  simp [sbVE, FMap.keys]

theorem sbVE_modify (s : FSub) (f g : ValEnv) : sbVE s (FMap.modify f g) = FMap.modify (sbVE s f) (sbVE s g) := by
  simp only [FMap.modify]
  rw [show sbVE s (g ++ _) = sbVE s g ++ sbVE s _ from List.map_append, sbVE_filter, sbVE_keys]

theorem sbVE_nil (s : FSub) : sbVE s [] = [] := rfl

theorem sbVE_plusAll (s : FSub) (l : List ValEnv) : sbVE s (FMap.plusAll l) = FMap.plusAll (l.map (sbVE s)) := by
  unfold FMap.plusAll
  suffices h : ∀ acc, sbVE s (l.foldl FMap.modify acc) = (l.map (sbVE s)).foldl FMap.modify (sbVE s acc) from h []
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; simp only [List.foldl_cons, List.map_cons]; rw [ih, sbVE_modify]

theorem sbScheme_mono (s : FSub) (τ : Ty) : sbScheme s (mono τ) = mono (sb s τ) := rfl

mutual
theorem sbAtPat_ve (s : FSub) : ∀ p : AAtPat, (sbAtPat s p).ve = sbVE s p.ve
  | .wild _ | .scon _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .var _ _ => rfl
  | .record r _ => by simp only [sbAtPat, AAtPat.ve, sbPatRowOpt_ve s r]
  | .tuple p1 p2 p3 => by
    simp only [sbAtPat, AAtPat.ve, sbPat_ve s p1, sbPat_ve s p2, sbPatOpt_ve s p3, sbVE_modify]
  | .paren p => by simp only [sbAtPat, AAtPat.ve, sbPat_ve s p]
theorem sbPatRow_ve (s : FSub) : ∀ r : APatRow, (sbPatRow s r).ve = sbVE s r.ve
  | .field _ _ rest => by simp only [sbPatRow, APatRow.ve, sbPatRowOpt_ve s rest, sbVE_modify]; rfl
theorem sbPatRowOpt_ve (s : FSub) : ∀ r : Option APatRow, APatRow.veOpt (sbPatRowOpt s r) = sbVE s (APatRow.veOpt r)
  | none => rfl
  | some r => by simp only [sbPatRowOpt, APatRow.veOpt, sbPatRow_ve s r]
theorem sbPat_ve (s : FSub) : ∀ p : APat, (sbPat s p).ve = sbVE s p.ve
  | .atpat a => by simp only [sbPat, APat.ve, sbAtPat_ve s a]
  | .con _ _ args _ => by simp only [sbPat, APat.ve, sbAtPats_veList s args, sbVE_plusAll]
  | .cons p1 p2 => by simp only [sbPat, APat.ve, sbPat_ve s p1, sbPat_ve s p2, sbVE_modify]
  | .as p _ => by simp only [sbPat, APat.ve, sbPat_ve s p, sbVE_modify, sbPat_ty s p]; rfl
theorem sbPatOpt_ve (s : FSub) : ∀ p : Option APat, APat.veOpt (sbPatOpt s p) = sbVE s (APat.veOpt p)
  | none => rfl
  | some p => by simp only [sbPatOpt, APat.veOpt, sbPat_ve s p]
theorem sbAtPats_veList (s : FSub) : ∀ l : List AAtPat, AAtPat.veList (sbAtPats s l) = (AAtPat.veList l).map (sbVE s)
  | [] => rfl
  | a :: as => by simp only [sbAtPats, AAtPat.veList, sbAtPat_ve s a, sbAtPats_veList s as, List.map_cons]
end

theorem sbRow_modifyF (s : FSub) : ∀ (f : Nat) (ρ ρ' : Row),
    sbRow s (Row.modifyF f ρ ρ') = Row.modifyF f (sbRow s ρ) (sbRow s ρ')
  | _, [], _ => by simp only [Row.modifyF, sbRow]
  | _, _ :: _, [] => by simp only [Row.modifyF, sbRow]
  | 0, _ :: _, _ :: _ => by simp only [Row.modifyF, sbRow, sbRow_eq, List.map_append, List.map_cons]
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [Row.modifyF, sbRow]
    split
    · simp only [sbRow, sbRow_modifyF s f r1 r2]
    · split
      · simp only [sbRow, sbRow_modifyF s f r1 ((l2, τ2) :: r2)]
      · simp only [sbRow, sbRow_modifyF s f ((l1, τ1) :: r1) r2]

theorem sbRow_length (s : FSub) (ρ : Row) : (sbRow s ρ).length = ρ.length := by
  rw [sbRow_eq]; simp

theorem sbRow_modify (s : FSub) (ρ ρ' : Row) : sbRow s (Row.modify ρ ρ') = Row.modify (sbRow s ρ) (sbRow s ρ') := by
  simp only [Row.modify, sbRow_modifyF, sbRow_length]

end StandardElm.Stat.Complete
