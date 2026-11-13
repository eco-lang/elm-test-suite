/-
  A Standard Definition of Elm? Mechanisation: termination of W for F_e (L13, milestone (e) of plan
  step 11), as WDTerm.lean for WD.lean's W: the group entries and the escape check use no fuel.
-/
import StandardElmMech.Stat.Complete.WE
import StandardElmMech.Stat.Complete.WDTerm

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

theorem groupEntriesD_ne_oof (C : Ctx) : ∀ (vb : BValBind) (st : WDSt), groupEntriesD C vb st ≠ .outOfFuel
  | .var _ none _ none, _ => by rw [groupEntriesD.eq_1]; noofD
  | .var _ none _ (some vb), _ => by
    rw [groupEntriesD.eq_1]; noofD
    all_goals exact groupEntriesD_ne_oof C vb _
  | .var _ (some ty) _ none, _ => by
    rw [groupEntriesD.eq_2]
    split
    · rcases elabTy (C.plusU (newU C.U ty)) ty with _ | τ
      · noofD
      · dsimp only
        split <;> noofD
    · noofD
  | .var _ (some ty) _ (some vb), _ => by
    rw [groupEntriesD.eq_2]
    split
    · rcases elabTy (C.plusU (newU C.U ty)) ty with _ | τ
      · noofD
      · dsimp only
        split <;> noofD
        all_goals exact groupEntriesD_ne_oof C vb _
    · noofD
  | .pat _ _, _ => fun h => by cases h

theorem groupEntriesD_stable (C : Ctx) (vb : BValBind) (st : WDSt) : StableAtD (fun _ => groupEntriesD C vb) st :=
  stableD_const (groupEntriesD_ne_oof C vb st)

section
variable (R : RRigid)

mutual
theorem wdAtExp_stable : ∀ (C : Ctx) (a : BAtExp) (st : WDSt), StableAtD (fun k => wdAtExp k R C a) st
  | _, .scon (.int _), st => by
    simp only [wdAtExp]; exact stableD_bind (stableD_freshC _ st) fun _ _ => stableD_pure _ _
  | _, .scon (.float _ _), st | _, .scon (.char _), st | _, .scon (.str _), st => by
    simp only [wdAtExp]; exact stableD_pure _ _
  | C, .var lv, st => by
    simp only [wdAtExp]
    rcases h : C.lookupVal lv with _ | ⟨σ, _⟩
    · exact stableD_fail _
    · exact stableD_bind (stableD_instantiate σ st) fun _ _ => stableD_pure _ _
  | C, .con lc, st => by
    simp only [wdAtExp]
    rcases h : C.lookupVal lc with _ | ⟨σ, _⟩
    · exact stableD_fail _
    · exact stableD_bind (stableD_instantiate σ st) fun _ _ => stableD_pure _ _
  | _, .op o, st => by
    simp only [wdAtExp]
    rcases h : OTstat o with _ | ⟨σ, _⟩
    · exact stableD_fail _
    · exact stableD_bind (stableD_instantiate σ st) fun _ _ => stableD_pure _ _
  | _, .unit, st => by simp only [wdAtExp]; exact stableD_pure _ _
  | C, .tuple e1 e2 e3, st => by
    simp only [wdAtExp]
    exact stableD_bind (wdExp_stable C e1 st) fun _ st1 => stableD_bind (wdExp_stable C e2 st1) fun _ st2 =>
      stableD_bind (wdExpOpt_stable C e3 st2) fun _ _ => stableD_pure _ _
  | _, .nil, st => by
    simp only [wdAtExp]; exact stableD_bind (stableD_freshV st) fun _ _ => stableD_pure _ _
  | C, .record row, st => by
    simp only [wdAtExp]
    exact stableD_bind (wdExpRowOpt_stable C row st) fun _ _ => stableD_pure _ _
  | C, .update x row, st => by
    simp only [wdAtExp]
    rcases h : C.lookupVal ⟨none, x⟩ with _ | ⟨σ, _⟩
    · exact stableD_fail _
    · exact stableD_bind (stableD_instantiate σ st) fun _ st1 => stableD_bind (wdExpRow_stable C row st1) fun _ st2 =>
        stableD_bind (stableD_freshRow st2) fun _ st3 => stableD_bind (stableD_unifyW R _ _ st3) fun _ _ =>
          stableD_pure _ _
  | C, .letE d e, st => by
    simp only [wdAtExp]
    exact stableD_bind (wdDec_stable C d st) fun _ st1 => stableD_bind (stableD_getθ st1) fun _ st2 =>
      stableD_bind (wdExp_stable _ e st2) fun _ _ => stableD_pure _ _
  | C, .paren e, st => by
    simp only [wdAtExp]; exact stableD_bind (wdExp_stable C e st) fun _ _ => stableD_pure _ _
theorem wdExp_stable : ∀ (C : Ctx) (e : BExp) (st : WDSt), StableAtD (fun k => wdExp k R C e) st
  | C, .atexp a, st => by
    simp only [wdExp]; exact stableD_bind (wdAtExp_stable C a st) fun _ _ => stableD_pure _ _
  | C, .app e a, st => by
    simp only [wdExp]
    exact stableD_bind (wdExp_stable C e st) fun _ st1 => stableD_bind (wdAtExp_stable C a st1) fun _ st2 =>
      stableD_bind (stableD_freshV st2) fun _ st3 => stableD_bind (stableD_unifyW R _ _ st3) fun _ _ =>
        stableD_pure _ _
  | C, .lam p e, st => by
    simp only [wdExp]
    exact stableD_bind (wdAtPat_stable R C p st) fun _ st1 => stableD_bind (wdExp_stable _ e st1) fun _ _ =>
      stableD_pure _ _
  | C, .caseE e m, st => by
    simp only [wdExp]
    exact stableD_bind (wdExp_stable C e st) fun _ st1 => stableD_bind (wdMatch_stable C m st1) fun _ st2 =>
      stableD_bind (stableD_freshV st2) fun _ st3 => stableD_bind (stableD_unifyW R _ _ st3) fun _ _ =>
        stableD_pure _ _
theorem wdExpRow_stable : ∀ (C : Ctx) (r : BExpRow) (st : WDSt), StableAtD (fun k => wdExpRow k R C r) st
  | C, .field _ e rest, st => by
    simp only [wdExpRow]
    exact stableD_bind (wdExp_stable C e st) fun _ st1 => stableD_bind (wdExpRowOpt_stable C rest st1) fun _ _ =>
      stableD_pure _ _
theorem wdExpRowOpt_stable : ∀ (C : Ctx) (r : Option BExpRow) (st : WDSt), StableAtD (fun k => wdExpRowOpt k R C r) st
  | _, none, st => by simp only [wdExpRowOpt]; exact stableD_pure _ _
  | C, some r, st => by
    simp only [wdExpRowOpt]; exact stableD_bind (wdExpRow_stable C r st) fun _ _ => stableD_pure _ _
theorem wdExpOpt_stable : ∀ (C : Ctx) (e : Option BExp) (st : WDSt), StableAtD (fun k => wdExpOpt k R C e) st
  | _, none, st => by simp only [wdExpOpt]; exact stableD_pure _ _
  | C, some e, st => by
    simp only [wdExpOpt]; exact stableD_bind (wdExp_stable C e st) fun _ _ => stableD_pure _ _
theorem wdMatch_stable : ∀ (C : Ctx) (m : BMatch) (st : WDSt), StableAtD (fun k => wdMatch k R C m) st
  | C, .mk mr rest, st => by
    simp only [wdMatch]
    exact stableD_bind (wdMRule_stable C mr st) fun _ st1 => stableD_bind (wdMatchOpt_stable C _ rest st1) fun _ _ =>
      stableD_pure _ _
theorem wdMatchOpt_stable : ∀ (C : Ctx) (τ : Ty) (m : Option BMatch) (st : WDSt),
    StableAtD (fun k => wdMatchOpt k R C τ m) st
  | _, _, none, st => by simp only [wdMatchOpt]; exact stableD_pure _ _
  | C, τ, some m, st => by
    simp only [wdMatchOpt]
    exact stableD_bind (wdMatch_stable C m st) fun _ st1 => stableD_bind (stableD_unifyW R _ _ st1) fun _ _ =>
      stableD_pure _ _
theorem wdMRule_stable : ∀ (C : Ctx) (mr : BMRule) (st : WDSt), StableAtD (fun k => wdMRule k R C mr) st
  | C, .mk p e, st => by
    simp only [wdMRule]
    exact stableD_bind (wdPat_stable R C p st) fun _ st1 => stableD_bind (wdExp_stable _ e st1) fun _ _ =>
      stableD_pure _ _
theorem wdDec_stable : ∀ (C : Ctx) (d : BDec) (st : WDSt), StableAtD (fun k => wdDec k R C d) st
  | C, .val (.pat p e), st => by
    simp only [wdDec]
    refine stableD_bind (wdAtPat_stable R C p st) fun r st1 => ?_
    rcases r with ⟨τp, ap⟩
    dsimp only
    by_cases hc : (ap.ve.all fun q => !conBound C q.1) = true
    · simp only [hc, ↓reduceIte]
      exact stableD_bind (wdExp_stable _ e st1) fun _ st2 => stableD_bind (stableD_unifyW R _ _ st2) fun _ _ => stableD_pure _ _
    · simp only [hc, ↓reduceIte]
      exact stableD_unsupported _
  | C, .val (.var x ann e rest), st => by
    simp only [wdDec]
    refine stableD_bind (groupEntriesD_stable C _ st) fun _ st1 =>
      stableD_bind (wdMembers_stable _ (.var x ann e rest) _ st1) fun _ st2 => stableD_bind (stableD_getθ st2) fun _ _ => ?_
    split
    · exact stableD_pure _ _
    · exact stableD_fail _
theorem wdMembers_stable : ∀ (Cg : Ctx) (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)) (st : WDSt),
    StableAtD (fun k => wdMembers k R Cg vb es) st
  | Cg, .var x _ e rest, (ann, τx) :: es, st => by
    simp only [wdMembers]
    exact stableD_bind (wdExp_stable _ e st) fun _ st1 => stableD_bind (stableD_unifyW R _ _ st1) fun _ st2 =>
      stableD_bind (wdMembersOpt_stable Cg rest es st2) fun _ _ => stableD_pure _ _
  | _, .var _ _ _ _, [], st => by simp only [wdMembers]; exact stableD_unsupported _
  | _, .pat _ _, _, st => by simp only [wdMembers]; exact stableD_unsupported _
theorem wdMembersOpt_stable : ∀ (Cg : Ctx) (vb : Option BValBind) (es : List (Option (BTy × List BVar) × Ty))
    (st : WDSt), StableAtD (fun k => wdMembersOpt k R Cg vb es) st
  | _, none, _, st => by simp only [wdMembersOpt]; exact stableD_pure _ _
  | Cg, some vb, es, st => by
    simp only [wdMembersOpt]; exact stableD_bind (wdMembers_stable Cg vb es st) fun _ _ => stableD_pure _ _
end

end

/-! ## L13 -/

/-- Termination of W (L13), with fuel monotonicity: from some fuel on, W's outcome on the root
    context is not `outOfFuel` and no longer changes. Unconditional (every phrase, every
    context). -/
theorem inferExpWD_terminates (C0 : Ctx) (e : BExp) :
    ∃ n, inferExpWD n C0 e ≠ .outOfFuel ∧ ∀ m, n ≤ m → inferExpWD m C0 e = inferExpWD n C0 e := by
  obtain ⟨N, hN, hmono⟩ := wdExp_stable (rigidFromD (freshAboveD C0)) C0 e ⟨[], freshAboveD C0⟩
  refine ⟨N, ?_, fun m hm => ?_⟩
  · rw [inferExpWD_eq]; unfold inferExpWDSpec
    simp only
    split
    · split
      · split <;> exact fun h => by cases h
      · exact fun h => by cases h
    · exact fun h => by cases h
    · exact fun h => by cases h
    · rename_i h; exact absurd h hN
  · simp only [inferExpWD_eq]; unfold inferExpWDSpec
    simp only [hmono m hm]


end WE

end StandardElm.Stat.Complete
