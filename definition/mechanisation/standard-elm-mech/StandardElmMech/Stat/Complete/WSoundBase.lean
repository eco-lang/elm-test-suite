/-
  A Standard Definition of Elm? Mechanisation: the bookkeeping for L10 (plan step 11, milestone
  (b), section 8): the checker accepts W's final result.

  The difficulty is the closure at a `let`: W closes the group's environment under the
  substitution `θ1` of that moment, and later `unify` steps refine the substitution; the checker
  closes the environment under the final substitution. The two closures agree when the variables
  generalised at the `let` ("dead" from then on) are never bound later nor put in the range of a
  binding of a variable of the context (`DeadC`). This file has the facts about substitutions
  that carry this through W:

  * `Moves P θ θ'`: every variable `θ'` binds that `θ` did not is in `P`, and so are the variables
    of its image. A `unify` step moves only variables of its equation (`uLoop_moves`); a phrase
    moves only variables reachable from its context or new (`Reach`), composed by `moves_trans`.
  * `Seg`: a segment of a run (counter, invariant, absorption, `Moves`).
  * `DeadC`: a constraint recorded at a closure, preserved by a segment that does not reach its
    generalised variables (`deadC_seg`).
-/
import StandardElmMech.Stat.Complete.WTerm

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-- `b` occurs in `τ`. -/
abbrev TV (b : TyVar) (τ : Ty) : Prop := BVar.ty b ∈ τ.vars

/-! ## Absorption -/

theorem absorbs_sb' {s θ : FSub} (h : Absorbs s θ) (τ : Ty) : sb s (sb θ τ) = sb s τ := by
  rw [sb_sb]; congr 1; funext a; exact h a

theorem absorbs_trans {s θ2 θ1 : FSub} (h2 : Absorbs s θ2) (h1 : Absorbs θ2 θ1) : Absorbs s θ1 := fun a => by
  rw [← absorbs_sb' h2 (θ1 a), h1 a]; exact h2 a

theorem absorbs_self {θ : FSub} (h : Idem θ) : Absorbs θ θ := fun a => sb_eq_self_iff.mpr (h a)

/-! ## Moves -/

/-- Every variable `θ'` binds that `θ` did not is in `P`, and so are the variables of its image. -/
def Moves (P : TyVar → Prop) (θ θ' : FSub) : Prop :=
  ∀ d, θ d = .var d → θ' d ≠ .var d → P d ∧ ∀ b, TV b (θ' d) → P b

theorem moves_refl (P : TyVar → Prop) (θ : FSub) : Moves P θ θ := fun _ h1 h2 => absurd h1 h2

theorem moves_mono {P Q : TyVar → Prop} {θ θ' : FSub} (h : Moves P θ θ') (hPQ : ∀ b, P b → Q b) :
    Moves Q θ θ' := fun d h1 h2 => ⟨hPQ _ (h d h1 h2).1, fun b hb => hPQ _ ((h d h1 h2).2 b hb)⟩

/-- A variable of an image under the later substitution: a variable of the image under the
    earlier one, fixed, or one of a moved variable's image. -/
theorem moves_ty {P : TyVar → Prop} {θ θ' : FSub} (hm : Moves P θ θ') (ha : Absorbs θ' θ) (hi : Idem θ)
    (τ : Ty) (b : TyVar) (hb : TV b (sb θ' τ)) :
    (TV b (sb θ τ) ∧ θ' b = .var b) ∨ ∃ e, TV e (sb θ τ) ∧ θ e = .var e ∧ θ' e ≠ .var e ∧ P e ∧ P b ∧ TV b (θ' e) := by
  rw [← absorbs_sb' ha] at hb
  obtain ⟨e, he, hbe⟩ := tyvar_sb hb
  have hθe : θ e = .var e := by
    obtain ⟨c, _, hc⟩ := tyvar_sb he; exact hi c e hc
  by_cases h : θ' e = .var e
  · rw [h] at hbe
    simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hbe; subst hbe
    exact .inl ⟨he, h⟩
  · exact .inr ⟨e, he, hθe, h, (hm e hθe h).1, (hm e hθe h).2 b hbe, hbe⟩

theorem moves_ty' {P : TyVar → Prop} {θ θ' : FSub} (hm : Moves P θ θ') (ha : Absorbs θ' θ) (hi : Idem θ)
    (τ : Ty) (b : TyVar) (hb : TV b (sb θ' τ)) : TV b (sb θ τ) ∨ P b := by
  rcases moves_ty hm ha hi τ b hb with h | ⟨_, _, _, _, _, h, _⟩
  · exact .inl h.1
  · exact .inr h

theorem moves_var {P : TyVar → Prop} {θ θ' : FSub} (hm : Moves P θ θ') (ha : Absorbs θ' θ) (hi : Idem θ)
    (x b : TyVar) (hb : TV b (θ' x)) : TV b (θ x) ∨ P b :=
  moves_ty' hm ha hi (.var x) b hb

/-- A variable outside `P` that a type's image avoids is avoided later. -/
theorem avoid_seg {P : TyVar → Prop} {θ θ' : FSub} (hm : Moves P θ θ') (ha : Absorbs θ' θ) (hi : Idem θ)
    {τ : Ty} {b : TyVar} (h1 : ¬ TV b (sb θ τ)) (h2 : ¬ P b) : ¬ TV b (sb θ' τ) := fun h =>
  (moves_ty' hm ha hi τ b h).elim h1 h2

theorem moves_trans {P : TyVar → Prop} {θ θ1 θ2 : FSub} (h1 : Moves P θ θ1) (h2 : Moves P θ1 θ2)
    (ha : Absorbs θ2 θ1) (hi : Idem θ1) : Moves P θ θ2 := by
  intro d hd hd2
  by_cases hd1 : θ1 d = .var d
  · exact h2 d hd1 hd2
  · refine ⟨(h1 d hd hd1).1, fun b hb => ?_⟩
    rcases moves_var h2 ha hi d b hb with h | h
    · exact (h1 d hd hd1).2 b h
    · exact h

/-! ## Unification moves only the variables of its equation and new ones -/

/-- MguCVars.lean's invariant, read as `Moves`. -/
theorem moves_of_inv {P : TyVar → Prop} {θ θ' : Bnd}
    (h : InvQP (fun d => lk θ d = .var d) P θ') : Moves P (lk θ) (lk θ') :=
  fun d h1 h2 => h d h1 h2

/-! ## Classes of W's variables -/

/-- Milestone (b) kept W's variables of class any; from milestone (c) on W creates variables of
    every class (integer constants, instances, refinements), and the closure handles them (A93,
    WSoundClos.lean). The predicate is kept, trivial, so that the bookkeeping below is unchanged. -/
def AnyV (_n0 : Nat) (_b : TyVar) : Prop := True

def AnyT (n0 : Nat) (τ : Ty) : Prop := ∀ b, TV b τ → AnyV n0 b

def SAny (n0 : Nat) (θ : FSub) : Prop := ∀ a b, θ a ≠ .var a → TV b (θ a) → AnyV n0 b

theorem anyT_sb {n0 : Nat} {θ : FSub} (_hθ : SAny n0 θ) {τ : Ty} (_hτ : AnyT n0 τ) : AnyT n0 (sb θ τ) :=
  fun _ _ => trivial

theorem sAny_all (n0 : Nat) (θ : FSub) : SAny n0 θ := fun _ _ _ _ => trivial

theorem anyT_of_vars_nil {n0 : Nat} {τ : Ty} (_h : τ.vars = []) : AnyT n0 τ := fun _ _ => trivial

theorem anyT_fresh (n0 n : Nat) {c : Cls} : AnyT n0 (.var (.fresh n c)) := fun _ _ => trivial

/-! ## Segments of a run -/

/-- A segment of a run from `st` to `st'` moving only variables in `P`. -/
structure Seg (n0 : Nat) (P : TyVar → Prop) (st st' : WSt) : Prop where
  le : st.n ≤ st'.n
  inv : SInv n0 st'
  any : SAny n0 (lk st'.θ)
  abs : Absorbs (lk st'.θ) (lk st.θ)
  mv : Moves P (lk st.θ) (lk st'.θ)

theorem Seg.refl {n0 : Nat} {P : TyVar → Prop} {st : WSt} (hi : SInv n0 st) (ha : SAny n0 (lk st.θ)) :
    Seg n0 P st st :=
  ⟨Nat.le_refl _, hi, ha, absorbs_self hi.good.idem, moves_refl _ _⟩

theorem Seg.trans {n0 : Nat} {P : TyVar → Prop} {st st1 st2 : WSt} (h1 : Seg n0 P st st1) (h2 : Seg n0 P st1 st2) :
    Seg n0 P st st2 :=
  ⟨Nat.le_trans h1.le h2.le, h2.inv, h2.any, absorbs_trans h2.abs h1.abs,
    moves_trans h1.mv h2.mv h2.abs h1.inv.good.idem⟩

theorem Seg.mono {n0 : Nat} {P Q : TyVar → Prop} {st st' : WSt} (h : Seg n0 P st st') (hPQ : ∀ b, P b → Q b) :
    Seg n0 Q st st' := ⟨h.le, h.inv, h.any, h.abs, moves_mono h.mv hPQ⟩

theorem seg_fresh {n0 : Nat} {P : TyVar → Prop} {st : WSt} (hi : SInv n0 st) (ha : SAny n0 (lk st.θ)) :
    Seg n0 P st { st with n := st.n + 1 } :=
  ⟨Nat.le_succ _, hi.fresh, ha, absorbs_self hi.good.idem, moves_refl _ _⟩

/-- `unify` in W's state: a segment moving only variables of the substituted equation and new
    ones; the new substitution unifies the two types. -/
theorem seg_unify {fuel n0 : Nat} {τ1 τ2 : Ty} {st st' : WSt} {u : Unit} (hi : SInv n0 st)
    (_hany : SAny n0 (lk st.θ)) (hτ1 : OkT st.n τ1) (hτ2 : OkT st.n τ2) (_ha1 : AnyT n0 τ1) (_ha2 : AnyT n0 τ2)
    (h : unifyW fuel (rigidFrom n0) τ1 τ2 st = .ok u st') :
    Seg n0 (fun b => TV b (sb (lk st.θ) τ1) ∨ TV b (sb (lk st.θ) τ2) ∨ b.isNew st.n = true) st st' ∧
      ∀ s, Absorbs s (lk st'.θ) → sb s τ1 = sb s τ2 := by
  have o1 : ∀ b, BVar.ty b ∈ τ1.vars → b.isNew st.n = false := fun b hb => by
    obtain ⟨c, e, -, h⟩ := hτ1 _ hb; cases e; exact h
  have o2 : ∀ b, BVar.ty b ∈ τ2.vars → b.isNew st.n = false := fun b hb => by
    obtain ⟨c, e, -, h⟩ := hτ2 _ hb; cases e; exact h
  have hN := newFlex_rigidFrom (n := st.n) hi.le
  obtain ⟨g', hn, hc, -⟩ := unifyW_ok hN hi.good o1 o2 h
  have hbnd := unifyW_bndOk hi hτ1 hτ2 h
  unfold unifyW at h
  split at h
  · rename_i θ' n' hu
    simp only [WOut.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    have hg := good_sb hi.good o1 o2
    have hab : Absorbs (lk θ') (lk st.θ) := (hc (lk θ') (absorbs_self g'.idem)).2
    have hm : Moves (fun b => TV b (sb (lk st.θ) τ1) ∨ TV b (sb (lk st.θ) τ2) ∨ b.isNew st.n = true)
        (lk st.θ) (lk θ') := moves_of_inv (cLoop_inv fuel _ _ _ _ _ hg
          (fun b hb => by
            obtain ⟨e, he, hbe⟩ := mem_bvars.mp hb
            simp only [List.mem_singleton] at he; subst he
            rcases hbe with hbe | hbe
            · exact .inl hbe
            · exact .inr (.inl hbe))
          (fun b hb => .inr (.inr hb)) (fun d h1 h2 => absurd h1 h2) hu)
    exact ⟨⟨hn, ⟨Nat.le_trans hi.le hn, g', hbnd⟩, sAny_all _ _, hab, hm⟩, fun s ha => (hc s ha).1⟩
  · cases h
  · cases h
  · cases h

end StandardElm.Stat.Complete
