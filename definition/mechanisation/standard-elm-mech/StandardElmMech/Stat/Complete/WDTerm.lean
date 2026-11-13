/-
  A Standard Definition of Elm? Mechanisation: termination of W for F_d (plan step 11, milestone
  (d), section 8, L13), as WTerm.lean for W: for every phrase and state there is a fuel from which
  `inferExpWD`'s outcome is not `outOfFuel` and no longer changes. Fuel is used only by unification
  with rows (`rLoop`), which terminates for every problem and is monotone in its fuel
  (`rLoop_terminates`, `rLoop_mono`, MguRTerm.lean).
-/
import StandardElmMech.Stat.Complete.WD

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

/-- From fuel `N` on, the outcome is not `outOfFuel` and does not change. -/
def StableAtD {α : Type} (M : Nat → WDM α) (st : WDSt) : Prop :=
  ∃ N, M N st ≠ .outOfFuel ∧ ∀ k, N ≤ k → M k st = M N st

theorem stableD_const {α : Type} {M : WDM α} {st : WDSt} (h : M st ≠ .outOfFuel) : StableAtD (fun _ => M) st :=
  ⟨0, h, fun _ _ => rfl⟩

theorem stableD_pure {α : Type} (a : α) (st : WDSt) : StableAtD (fun _ => (pure a : WDM α)) st :=
  stableD_const (fun h => by cases h)

theorem stableD_fail {α : Type} (st : WDSt) : StableAtD (fun _ => (wdFail : WDM α)) st :=
  stableD_const (fun h => by cases h)

theorem stableD_unsupported {α : Type} (st : WDSt) : StableAtD (fun _ => (wdUnsupported : WDM α)) st :=
  stableD_const (fun h => by cases h)

theorem stableD_freshV (st : WDSt) : StableAtD (fun _ => freshVD) st := stableD_const (fun h => by cases h)

theorem stableD_freshC (c : Cls) (st : WDSt) : StableAtD (fun _ => freshCD c) st := stableD_const (fun h => by cases h)

theorem stableD_getθ (st : WDSt) : StableAtD (fun _ => getθD) st := stableD_const (fun h => by cases h)

theorem stableD_bind {α β : Type} {M : Nat → WDM α} {F : Nat → α → WDM β} {st : WDSt}
    (hM : StableAtD M st) (hF : ∀ a st', StableAtD (fun k => F k a) st') :
    StableAtD (fun k => M k >>= F k) st := by
  obtain ⟨N1, h1, e1⟩ := hM
  cases hr : M N1 st with
  | ok a st' =>
    obtain ⟨N2, h2, e2⟩ := hF a st'
    refine ⟨max N1 N2, ?_, fun k hk => ?_⟩
    · show WDM.bind (M (max N1 N2)) (F (max N1 N2)) st ≠ _
      simp only [WDM.bind, e1 _ (Nat.le_max_left _ _), hr, e2 _ (Nat.le_max_right _ _)]
      exact h2
    · show WDM.bind (M k) (F k) st = WDM.bind (M (max N1 N2)) (F (max N1 N2)) st
      simp only [WDM.bind, e1 _ (Nat.le_trans (Nat.le_max_left _ _) hk), e1 _ (Nat.le_max_left _ _), hr,
        e2 _ (Nat.le_trans (Nat.le_max_right _ _) hk), e2 _ (Nat.le_max_right _ _)]
  | fail =>
    refine ⟨N1, ?_, fun k hk => ?_⟩
    · show WDM.bind (M N1) (F N1) st ≠ _
      simp only [WDM.bind, hr]; exact fun h => by cases h
    · show WDM.bind (M k) (F k) st = WDM.bind (M N1) (F N1) st
      simp only [WDM.bind, e1 _ hk, hr]
  | unsupported =>
    refine ⟨N1, ?_, fun k hk => ?_⟩
    · show WDM.bind (M N1) (F N1) st ≠ _
      simp only [WDM.bind, hr]; exact fun h => by cases h
    · show WDM.bind (M k) (F k) st = WDM.bind (M N1) (F N1) st
      simp only [WDM.bind, e1 _ hk, hr]
  | outOfFuel => exact absurd hr h1

theorem stableD_freshRow (st : WDSt) : StableAtD (fun _ => freshRowD) st := stableD_const (fun h => by cases h)

theorem stableD_unifyW (R : RRigid) (τ1 τ2 : Ty) (st : WDSt) : StableAtD (fun k => unifyWD k R τ1 τ2) st := by
  obtain ⟨N, hN⟩ := rLoop_terminates R st.n st.θ [(rsb (toRS st.θ) τ1, rsb (toRS st.θ) τ2)] []
  refine ⟨N, ?_, fun k hk => ?_⟩
  · simp only [unifyWD]
    split
    · exact fun h => by cases h
    · exact fun h => by cases h
    · rename_i h; exact absurd h hN
  · have := rLoop_mono N (k - N) _ _ _ _ hN
    rw [Nat.add_sub_cancel' hk] at this
    simp only [unifyWD, this]

theorem stableD_instVars : ∀ (vs : List BVar) (st : WDSt), StableAtD (fun _ => instVarsD vs) st
  | [], st => stableD_pure _ st
  | .ty a :: rest, st => by
    simp only [instVarsD]
    exact stableD_bind (stableD_freshC _ st) fun _ st1 =>
      stableD_bind (stableD_instVars rest st1) fun _ _ => stableD_pure _ _
  | .row _ :: rest, st => by
    simp only [instVarsD]
    exact stableD_bind (stableD_freshRow st) fun _ st1 =>
      stableD_bind (stableD_instVars rest st1) fun _ _ => stableD_pure _ _

theorem stableD_instantiate (σ : Scheme) (st : WDSt) : StableAtD (fun _ => instantiateD σ) st := by
  simp only [instantiateD]
  refine stableD_bind (stableD_instVars _ st) fun ts st1 => ?_
  split
  · split
    · exact stableD_pure _ _
    · exact stableD_unsupported _
  · exact stableD_unsupported _

theorem noOofD_bind {α β : Type} {M : WDM α} {F : α → WDM β} {st : WDSt} (h1 : M st ≠ .outOfFuel)
    (h2 : ∀ a st', F a st' ≠ .outOfFuel) : (M >>= F) st ≠ .outOfFuel := by
  show WDM.bind M F st ≠ _
  simp only [WDM.bind]
  split
  · exact h2 _ _
  · exact fun h => by cases h
  · exact fun h => by cases h
  · rename_i h; exact absurd h h1

/-- Close goals `M st ≠ .outOfFuel` for a computation without fuel. -/
macro "noofD" : tactic => `(tactic| repeat' (first
  | (intro h; cases h; done)
  | (refine noOofD_bind ?_ fun _ _ => ?_)))

theorem groupEntriesD_ne_oof (C : Ctx) : ∀ (vb : BValBind) (st : WDSt), groupEntriesD C vb st ≠ .outOfFuel
  | .var _ none _ none, _ => by rw [groupEntriesD.eq_1]; noofD
  | .var _ none _ (some vb), _ => by
    rw [groupEntriesD.eq_1]; noofD
    all_goals exact groupEntriesD_ne_oof C vb _
  | .var _ (some ty) _ none, _ => by
    rw [groupEntriesD.eq_2]
    split
    · rcases elabTy (C.plusU []) ty with _ | τ
      · noofD
      · dsimp only
        split <;> noofD
    · noofD
  | .var _ (some ty) _ (some vb), _ => by
    rw [groupEntriesD.eq_2]
    split
    · rcases elabTy (C.plusU []) ty with _ | τ
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

theorem unifyArgsD_stable : ∀ (ts us : List Ty) (st : WDSt), StableAtD (fun k => unifyArgsD k R ts us) st
  | [], [], st => stableD_pure _ st
  | t :: ts, u :: us, st => by
    simp only [unifyArgsD]
    exact stableD_bind (stableD_unifyW R t u st) fun _ st1 => unifyArgsD_stable ts us st1
  | [], _ :: _, st => stableD_unsupported st
  | _ :: _, [], st => stableD_unsupported st

mutual
theorem wdAtPat_stable (C : Ctx) : ∀ (p : BAtPat) (st : WDSt), StableAtD (fun k => wdAtPat k R C p) st
  | .wild, st => by
    simp only [wdAtPat]; exact stableD_bind (stableD_freshV st) fun _ _ => stableD_pure _ _
  | .scon (.int _), st | .scon (.char _), st | .scon (.str _), st => by
    simp only [wdAtPat]; exact stableD_pure _ _
  | .scon (.float _ _), st => by simp only [wdAtPat]; exact stableD_fail _
  | .var _, st => by
    simp only [wdAtPat]; exact stableD_bind (stableD_freshV st) fun _ _ => stableD_pure _ _
  | .con lc, st => by
    simp only [wdAtPat]
    rcases h : C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · exact stableD_fail _
    · refine stableD_bind (stableD_instantiate σ st) fun ⟨ts, τ⟩ st1 => ?_
      cases τ <;> first | exact stableD_pure _ _ | exact stableD_unsupported _ | exact stableD_fail _
    · exact stableD_fail _
  | .unit, st => by simp only [wdAtPat]; exact stableD_pure _ _
  | .tuple p1 p2 p3, st => by
    simp only [wdAtPat]
    exact stableD_bind (wdPat_stable C p1 st) fun _ st1 => stableD_bind (wdPat_stable C p2 st1) fun _ st2 =>
      stableD_bind (wdPatOpt_stable C p3 st2) fun _ _ => stableD_pure _ _
  | .nil, st => by
    simp only [wdAtPat]; exact stableD_bind (stableD_freshV st) fun _ _ => stableD_pure _ _
  | .record row, st => by
    simp only [wdAtPat]
    exact stableD_bind (wdPatRowOpt_stable row st) fun _ st1 => stableD_bind (stableD_freshRow st1) fun _ _ =>
      stableD_pure _ _
  | .paren p, st => by
    simp only [wdAtPat]; exact stableD_bind (wdPat_stable C p st) fun _ _ => stableD_pure _ _
theorem wdPat_stable (C : Ctx) : ∀ (p : BPat) (st : WDSt), StableAtD (fun k => wdPat k R C p) st
  | .atpat a, st => by
    simp only [wdPat]; exact stableD_bind (wdAtPat_stable C a st) fun _ _ => stableD_pure _ _
  | .con lc args, st => by
    simp only [wdPat]
    rcases h : C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · exact stableD_fail _
    · refine stableD_bind (stableD_instantiate σ st) fun ⟨ts, τb⟩ st1 => ?_
      rcases hp : peel args.length τb with _ | ⟨τs, τr⟩
      · cases peelStuckVar args.length τb
        · exact stableD_fail _
        · exact stableD_unsupported _
      · cases τr <;> first | exact stableD_unsupported _ | exact stableD_fail _ |
          exact stableD_bind (wdAtPats_stable C args st1) fun _ st2 =>
            stableD_bind (unifyArgsD_stable R _ _ st2) fun _ _ => stableD_pure _ _
    · exact stableD_fail _
  | .cons p1 p2, st => by
    simp only [wdPat]
    exact stableD_bind (wdPat_stable C p1 st) fun _ st1 => stableD_bind (wdPat_stable C p2 st1) fun _ st2 =>
      stableD_bind (stableD_unifyW R _ _ st2) fun _ _ => stableD_pure _ _
  | .as p _, st => by
    simp only [wdPat]; exact stableD_bind (wdPat_stable C p st) fun _ _ => stableD_pure _ _
theorem wdPatOpt_stable (C : Ctx) : ∀ (p : Option BPat) (st : WDSt), StableAtD (fun k => wdPatOpt k R C p) st
  | none, st => by simp only [wdPatOpt]; exact stableD_pure _ _
  | some p, st => by
    simp only [wdPatOpt]; exact stableD_bind (wdPat_stable C p st) fun _ _ => stableD_pure _ _
theorem wdPatRow_stable : ∀ (r : BPatRow) (st : WDSt), StableAtD (fun k => wdPatRow k R r) st
  | .field _ rest, st => by
    simp only [wdPatRow]
    exact stableD_bind (stableD_freshV st) fun _ st1 => stableD_bind (wdPatRowOpt_stable rest st1) fun _ _ =>
      stableD_pure _ _
theorem wdPatRowOpt_stable : ∀ (r : Option BPatRow) (st : WDSt), StableAtD (fun k => wdPatRowOpt k R r) st
  | none, st => by simp only [wdPatRowOpt]; exact stableD_pure _ _
  | some r, st => by
    simp only [wdPatRowOpt]; exact stableD_bind (wdPatRow_stable r st) fun _ _ => stableD_pure _ _
theorem wdAtPats_stable (C : Ctx) : ∀ (l : List BAtPat) (st : WDSt), StableAtD (fun k => wdAtPats k R C l) st
  | [], st => by simp only [wdAtPats]; exact stableD_pure _ _
  | a :: as, st => by
    simp only [wdAtPats]
    exact stableD_bind (wdAtPat_stable C a st) fun _ st1 => stableD_bind (wdAtPats_stable C as st1) fun _ _ =>
      stableD_pure _ _
end

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
    exact stableD_bind (groupEntriesD_stable C _ st) fun _ st1 =>
      stableD_bind (wdMembers_stable _ (.var x ann e rest) _ st1) fun _ _ => stableD_pure _ _
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
  · unfold inferExpWD
    simp only
    split
    · split
      · split <;> exact fun h => by cases h
      · exact fun h => by cases h
    · exact fun h => by cases h
    · exact fun h => by cases h
    · rename_i h; exact absurd h hN
  · unfold inferExpWD
    simp only [hmono m hm]

end StandardElm.Stat.Complete
