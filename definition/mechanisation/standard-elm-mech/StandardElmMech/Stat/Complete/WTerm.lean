/-
  A Standard Definition of Elm? Mechanisation: termination of W (plan step 11, milestone (b),
  section 8, L13): for every phrase and state there is a fuel from which W's outcome is not
  `outOfFuel` and no longer changes (`StableAt`). Fuel is used only by `unify` (Mgu.lean's
  loop), which terminates for some fuel and is monotone in it (`uLoop_terminates`, `uLoop_mono`,
  MguTerm.lean); the rest is structural on the phrase, each `bind` taking the larger of the fuels
  of its two parts.
-/
import StandardElmMech.Stat.Complete.WPrincipality

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-- From fuel `N` on, the outcome is not `outOfFuel` and does not change. -/
def StableAt {α : Type} (M : Nat → WM α) (st : WSt) : Prop :=
  ∃ N, M N st ≠ .outOfFuel ∧ ∀ k, N ≤ k → M k st = M N st

theorem stable_const {α : Type} {M : WM α} {st : WSt} (h : M st ≠ .outOfFuel) : StableAt (fun _ => M) st :=
  ⟨0, h, fun _ _ => rfl⟩

theorem stable_pure {α : Type} (a : α) (st : WSt) : StableAt (fun _ => (pure a : WM α)) st :=
  stable_const (fun h => by cases h)

theorem stable_fail {α : Type} (st : WSt) : StableAt (fun _ => (wFail : WM α)) st :=
  stable_const (fun h => by cases h)

theorem stable_unsupported {α : Type} (st : WSt) : StableAt (fun _ => (wUnsupported : WM α)) st :=
  stable_const (fun h => by cases h)

theorem stable_freshV (st : WSt) : StableAt (fun _ => freshV) st := stable_const (fun h => by cases h)

theorem stable_freshC (c : Cls) (st : WSt) : StableAt (fun _ => freshC c) st := stable_const (fun h => by cases h)

theorem stable_getθ (st : WSt) : StableAt (fun _ => getθ) st := stable_const (fun h => by cases h)

theorem stable_bind {α β : Type} {M : Nat → WM α} {F : Nat → α → WM β} {st : WSt}
    (hM : StableAt M st) (hF : ∀ a st', StableAt (fun k => F k a) st') :
    StableAt (fun k => M k >>= F k) st := by
  obtain ⟨N1, h1, e1⟩ := hM
  cases hr : M N1 st with
  | ok a st' =>
    obtain ⟨N2, h2, e2⟩ := hF a st'
    refine ⟨max N1 N2, ?_, fun k hk => ?_⟩
    · show WM.bind (M (max N1 N2)) (F (max N1 N2)) st ≠ _
      simp only [WM.bind, e1 _ (Nat.le_max_left _ _), hr, e2 _ (Nat.le_max_right _ _)]
      exact h2
    · show WM.bind (M k) (F k) st = WM.bind (M (max N1 N2)) (F (max N1 N2)) st
      simp only [WM.bind, e1 _ (Nat.le_trans (Nat.le_max_left _ _) hk), e1 _ (Nat.le_max_left _ _), hr,
        e2 _ (Nat.le_trans (Nat.le_max_right _ _) hk), e2 _ (Nat.le_max_right _ _)]
  | fail =>
    refine ⟨N1, ?_, fun k hk => ?_⟩
    · show WM.bind (M N1) (F N1) st ≠ _
      simp only [WM.bind, hr]; exact fun h => by cases h
    · show WM.bind (M k) (F k) st = WM.bind (M N1) (F N1) st
      simp only [WM.bind, e1 _ hk, hr]
  | unsupported =>
    refine ⟨N1, ?_, fun k hk => ?_⟩
    · show WM.bind (M N1) (F N1) st ≠ _
      simp only [WM.bind, hr]; exact fun h => by cases h
    · show WM.bind (M k) (F k) st = WM.bind (M N1) (F N1) st
      simp only [WM.bind, e1 _ hk, hr]
  | outOfFuel => exact absurd hr h1

theorem stable_unifyW (R : Rigid) (τ1 τ2 : Ty) (st : WSt) : StableAt (fun k => unifyW k R τ1 τ2) st := by
  obtain ⟨N, hN⟩ := cLoop_terminates R st.n st.θ [(sb (lk st.θ) τ1, sb (lk st.θ) τ2)]
  refine ⟨N, ?_, fun k hk => ?_⟩
  · simp only [unifyW]
    split
    · exact fun h => by cases h
    · exact fun h => by cases h
    · exact fun h => by cases h
    · rename_i h; exact absurd h hN
  · have := cLoop_mono N (k - N) _ _ _ hN
    rw [Nat.add_sub_cancel' hk] at this
    simp only [unifyW, this]

theorem stable_instVars : ∀ (vs : List BVar) (st : WSt), StableAt (fun _ => instVars vs) st
  | [], st => stable_pure _ st
  | .ty a :: rest, st => by
    simp only [instVars]
    exact stable_bind (stable_freshC _ st) fun _ st1 =>
      stable_bind (stable_instVars rest st1) fun _ _ => stable_pure _ _
  | .row _ :: _, st => stable_unsupported st

theorem stable_instantiate (σ : Scheme) (st : WSt) : StableAt (fun _ => instantiate σ) st := by
  simp only [instantiate]
  refine stable_bind (stable_instVars _ st) fun ts st1 => ?_
  split
  · split
    · exact stable_pure _ _
    · exact stable_unsupported _
  · exact stable_unsupported _

theorem noOof_bind {α β : Type} {M : WM α} {F : α → WM β} {st : WSt} (h1 : M st ≠ .outOfFuel)
    (h2 : ∀ a st', F a st' ≠ .outOfFuel) : (M >>= F) st ≠ .outOfFuel := by
  show WM.bind M F st ≠ _
  simp only [WM.bind]
  split
  · exact h2 _ _
  · exact fun h => by cases h
  · exact fun h => by cases h
  · rename_i h; exact absurd h h1

/-- Close goals `M st ≠ .outOfFuel` for a computation without fuel. -/
macro "noof" : tactic => `(tactic| repeat' (first
  | (intro h; cases h; done)
  | (refine noOof_bind ?_ fun _ _ => ?_)))

theorem groupEntries_ne_oof (C : Ctx) : ∀ (vb : BValBind) (st : WSt), groupEntries C vb st ≠ .outOfFuel
  | .var _ none _ none, _ => by rw [groupEntries.eq_1]; noof
  | .var _ none _ (some vb), _ => by
    rw [groupEntries.eq_1]; noof
    all_goals exact groupEntries_ne_oof C vb _
  | .var _ (some ty) _ none, _ => by
    rw [groupEntries.eq_2]
    split
    · rcases elabTy (C.plusU []) ty with _ | τ
      · noof
      · dsimp only
        split <;> noof
    · noof
  | .var _ (some ty) _ (some vb), _ => by
    rw [groupEntries.eq_2]
    split
    · rcases elabTy (C.plusU []) ty with _ | τ
      · noof
      · dsimp only
        split <;> noof
        all_goals exact groupEntries_ne_oof C vb _
    · noof
  | .pat _ _, _ => fun h => by cases h

theorem groupEntries_stable (C : Ctx) (vb : BValBind) (st : WSt) : StableAt (fun _ => groupEntries C vb) st :=
  stable_const (groupEntries_ne_oof C vb st)

section
variable (R : Rigid)

theorem unifyArgs_stable : ∀ (ts us : List Ty) (st : WSt), StableAt (fun k => unifyArgs k R ts us) st
  | [], [], st => stable_pure _ st
  | t :: ts, u :: us, st => by
    simp only [unifyArgs]
    exact stable_bind (stable_unifyW R t u st) fun _ st1 => unifyArgs_stable ts us st1
  | [], _ :: _, st => stable_unsupported st
  | _ :: _, [], st => stable_unsupported st

mutual
theorem wAtPat_stable (C : Ctx) : ∀ (p : BAtPat) (st : WSt), StableAt (fun k => wAtPat k R C p) st
  | .wild, st => by
    simp only [wAtPat]; exact stable_bind (stable_freshV st) fun _ _ => stable_pure _ _
  | .scon (.int _), st | .scon (.char _), st | .scon (.str _), st => by
    simp only [wAtPat]; exact stable_pure _ _
  | .scon (.float _ _), st => by simp only [wAtPat]; exact stable_fail _
  | .var _, st => by
    simp only [wAtPat]; exact stable_bind (stable_freshV st) fun _ _ => stable_pure _ _
  | .con lc, st => by
    simp only [wAtPat]
    rcases h : C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · exact stable_fail _
    · refine stable_bind (stable_instantiate σ st) fun ⟨ts, τ⟩ st1 => ?_
      cases τ <;> first | exact stable_pure _ _ | exact stable_unsupported _ | exact stable_fail _
    · exact stable_fail _
  | .unit, st => by simp only [wAtPat]; exact stable_pure _ _
  | .tuple p1 p2 p3, st => by
    simp only [wAtPat]
    exact stable_bind (wPat_stable C p1 st) fun _ st1 => stable_bind (wPat_stable C p2 st1) fun _ st2 =>
      stable_bind (wPatOpt_stable C p3 st2) fun _ _ => stable_pure _ _
  | .nil, st => by
    simp only [wAtPat]; exact stable_bind (stable_freshV st) fun _ _ => stable_pure _ _
  | .record _, st => by simp only [wAtPat]; exact stable_unsupported _
  | .paren p, st => by
    simp only [wAtPat]; exact stable_bind (wPat_stable C p st) fun _ _ => stable_pure _ _
theorem wPat_stable (C : Ctx) : ∀ (p : BPat) (st : WSt), StableAt (fun k => wPat k R C p) st
  | .atpat a, st => by
    simp only [wPat]; exact stable_bind (wAtPat_stable C a st) fun _ _ => stable_pure _ _
  | .con lc args, st => by
    simp only [wPat]
    rcases h : C.lookupVal lc with _ | ⟨σ, _ | _⟩
    · exact stable_fail _
    · refine stable_bind (stable_instantiate σ st) fun ⟨ts, τb⟩ st1 => ?_
      rcases hp : peel args.length τb with _ | ⟨τs, τr⟩
      · cases peelStuckVar args.length τb
        · exact stable_fail _
        · exact stable_unsupported _
      · cases τr <;> first | exact stable_unsupported _ | exact stable_fail _ |
          exact stable_bind (wAtPats_stable C args st1) fun _ st2 =>
            stable_bind (unifyArgs_stable R _ _ st2) fun _ _ => stable_pure _ _
    · exact stable_fail _
  | .cons p1 p2, st => by
    simp only [wPat]
    exact stable_bind (wPat_stable C p1 st) fun _ st1 => stable_bind (wPat_stable C p2 st1) fun _ st2 =>
      stable_bind (stable_unifyW R _ _ st2) fun _ _ => stable_pure _ _
  | .as p _, st => by
    simp only [wPat]; exact stable_bind (wPat_stable C p st) fun _ _ => stable_pure _ _
theorem wPatOpt_stable (C : Ctx) : ∀ (p : Option BPat) (st : WSt), StableAt (fun k => wPatOpt k R C p) st
  | none, st => by simp only [wPatOpt]; exact stable_pure _ _
  | some p, st => by
    simp only [wPatOpt]; exact stable_bind (wPat_stable C p st) fun _ _ => stable_pure _ _
theorem wAtPats_stable (C : Ctx) : ∀ (l : List BAtPat) (st : WSt), StableAt (fun k => wAtPats k R C l) st
  | [], st => by simp only [wAtPats]; exact stable_pure _ _
  | a :: as, st => by
    simp only [wAtPats]
    exact stable_bind (wAtPat_stable C a st) fun _ st1 => stable_bind (wAtPats_stable C as st1) fun _ _ =>
      stable_pure _ _
end

mutual
theorem wAtExp_stable : ∀ (C : Ctx) (a : BAtExp) (st : WSt), StableAt (fun k => wAtExp k R C a) st
  | _, .scon (.int _), st => by
    simp only [wAtExp]; exact stable_bind (stable_freshC _ st) fun _ _ => stable_pure _ _
  | _, .scon (.float _ _), st | _, .scon (.char _), st | _, .scon (.str _), st => by
    simp only [wAtExp]; exact stable_pure _ _
  | C, .var lv, st => by
    simp only [wAtExp]
    rcases h : C.lookupVal lv with _ | ⟨σ, _⟩
    · exact stable_fail _
    · exact stable_bind (stable_instantiate σ st) fun _ _ => stable_pure _ _
  | C, .con lc, st => by
    simp only [wAtExp]
    rcases h : C.lookupVal lc with _ | ⟨σ, _⟩
    · exact stable_fail _
    · exact stable_bind (stable_instantiate σ st) fun _ _ => stable_pure _ _
  | _, .op o, st => by
    simp only [wAtExp]
    rcases h : OTstat o with _ | ⟨σ, _⟩
    · exact stable_fail _
    · exact stable_bind (stable_instantiate σ st) fun _ _ => stable_pure _ _
  | _, .unit, st => by simp only [wAtExp]; exact stable_pure _ _
  | C, .tuple e1 e2 e3, st => by
    simp only [wAtExp]
    exact stable_bind (wExp_stable C e1 st) fun _ st1 => stable_bind (wExp_stable C e2 st1) fun _ st2 =>
      stable_bind (wExpOpt_stable C e3 st2) fun _ _ => stable_pure _ _
  | _, .nil, st => by
    simp only [wAtExp]; exact stable_bind (stable_freshV st) fun _ _ => stable_pure _ _
  | _, .record _, st => by simp only [wAtExp]; exact stable_unsupported _
  | _, .update _ _, st => by simp only [wAtExp]; exact stable_unsupported _
  | C, .letE d e, st => by
    simp only [wAtExp]
    exact stable_bind (wDec_stable C d st) fun _ st1 => stable_bind (stable_getθ st1) fun _ st2 =>
      stable_bind (wExp_stable _ e st2) fun _ _ => stable_pure _ _
  | C, .paren e, st => by
    simp only [wAtExp]; exact stable_bind (wExp_stable C e st) fun _ _ => stable_pure _ _
theorem wExp_stable : ∀ (C : Ctx) (e : BExp) (st : WSt), StableAt (fun k => wExp k R C e) st
  | C, .atexp a, st => by
    simp only [wExp]; exact stable_bind (wAtExp_stable C a st) fun _ _ => stable_pure _ _
  | C, .app e a, st => by
    simp only [wExp]
    exact stable_bind (wExp_stable C e st) fun _ st1 => stable_bind (wAtExp_stable C a st1) fun _ st2 =>
      stable_bind (stable_freshV st2) fun _ st3 => stable_bind (stable_unifyW R _ _ st3) fun _ _ =>
        stable_pure _ _
  | C, .lam p e, st => by
    simp only [wExp]
    exact stable_bind (wAtPat_stable R C p st) fun _ st1 => stable_bind (wExp_stable _ e st1) fun _ _ =>
      stable_pure _ _
  | C, .caseE e m, st => by
    simp only [wExp]
    exact stable_bind (wExp_stable C e st) fun _ st1 => stable_bind (wMatch_stable C m st1) fun _ st2 =>
      stable_bind (stable_freshV st2) fun _ st3 => stable_bind (stable_unifyW R _ _ st3) fun _ _ =>
        stable_pure _ _
theorem wExpOpt_stable : ∀ (C : Ctx) (e : Option BExp) (st : WSt), StableAt (fun k => wExpOpt k R C e) st
  | _, none, st => by simp only [wExpOpt]; exact stable_pure _ _
  | C, some e, st => by
    simp only [wExpOpt]; exact stable_bind (wExp_stable C e st) fun _ _ => stable_pure _ _
theorem wMatch_stable : ∀ (C : Ctx) (m : BMatch) (st : WSt), StableAt (fun k => wMatch k R C m) st
  | C, .mk mr rest, st => by
    simp only [wMatch]
    exact stable_bind (wMRule_stable C mr st) fun _ st1 => stable_bind (wMatchOpt_stable C _ rest st1) fun _ _ =>
      stable_pure _ _
theorem wMatchOpt_stable : ∀ (C : Ctx) (τ : Ty) (m : Option BMatch) (st : WSt),
    StableAt (fun k => wMatchOpt k R C τ m) st
  | _, _, none, st => by simp only [wMatchOpt]; exact stable_pure _ _
  | C, τ, some m, st => by
    simp only [wMatchOpt]
    exact stable_bind (wMatch_stable C m st) fun _ st1 => stable_bind (stable_unifyW R _ _ st1) fun _ _ =>
      stable_pure _ _
theorem wMRule_stable : ∀ (C : Ctx) (mr : BMRule) (st : WSt), StableAt (fun k => wMRule k R C mr) st
  | C, .mk p e, st => by
    simp only [wMRule]
    exact stable_bind (wPat_stable R C p st) fun _ st1 => stable_bind (wExp_stable _ e st1) fun _ _ =>
      stable_pure _ _
theorem wDec_stable : ∀ (C : Ctx) (d : BDec) (st : WSt), StableAt (fun k => wDec k R C d) st
  | C, .val (.pat p e), st => by
    simp only [wDec]
    refine stable_bind (wAtPat_stable R C p st) fun r st1 => ?_
    rcases r with ⟨τp, ap⟩
    dsimp only
    by_cases hc : (ap.ve.all fun q => !conBound C q.1) = true
    · simp only [hc, ↓reduceIte]
      exact stable_bind (wExp_stable _ e st1) fun _ st2 => stable_bind (stable_unifyW R _ _ st2) fun _ _ => stable_pure _ _
    · simp only [hc, ↓reduceIte]
      exact stable_unsupported _
  | C, .val (.var x ann e rest), st => by
    simp only [wDec]
    exact stable_bind (groupEntries_stable C _ st) fun _ st1 =>
      stable_bind (wMembers_stable _ (.var x ann e rest) _ st1) fun _ _ => stable_pure _ _
theorem wMembers_stable : ∀ (Cg : Ctx) (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)) (st : WSt),
    StableAt (fun k => wMembers k R Cg vb es) st
  | Cg, .var x _ e rest, (ann, τx) :: es, st => by
    simp only [wMembers]
    exact stable_bind (wExp_stable _ e st) fun _ st1 => stable_bind (stable_unifyW R _ _ st1) fun _ st2 =>
      stable_bind (wMembersOpt_stable Cg rest es st2) fun _ _ => stable_pure _ _
  | _, .var _ _ _ _, [], st => by simp only [wMembers]; exact stable_unsupported _
  | _, .pat _ _, _, st => by simp only [wMembers]; exact stable_unsupported _
theorem wMembersOpt_stable : ∀ (Cg : Ctx) (vb : Option BValBind) (es : List (Option (BTy × List BVar) × Ty))
    (st : WSt), StableAt (fun k => wMembersOpt k R Cg vb es) st
  | _, none, _, st => by simp only [wMembersOpt]; exact stable_pure _ _
  | Cg, some vb, es, st => by
    simp only [wMembersOpt]; exact stable_bind (wMembers_stable Cg vb es st) fun _ _ => stable_pure _ _
end

end

/-! ## L13 -/

/-- Termination of W (L13), with fuel monotonicity: from some fuel on, W's outcome on the root
    context is not `outOfFuel` and no longer changes. Unconditional (every phrase, every
    context). -/
theorem inferExpW_terminates (C0 : Ctx) (e : BExp) :
    ∃ n, inferExpW n C0 e ≠ .outOfFuel ∧ ∀ m, n ≤ m → inferExpW m C0 e = inferExpW n C0 e := by
  obtain ⟨N, hN, hmono⟩ := wExp_stable (rigidFrom (freshAbove C0)) C0 e ⟨[], freshAbove C0⟩
  refine ⟨N, ?_, fun m hm => ?_⟩
  · unfold inferExpW
    simp only
    split
    · split <;> exact fun h => by cases h
    · exact fun h => by cases h
    · exact fun h => by cases h
    · rename_i h; exact absurd h hN
  · unfold inferExpW
    simp only [hmono m hm]

/-! ## Erasure of a substituted phrase -/

mutual
theorem sbAtPat_erase (s : FSub) : ∀ p : AAtPat, (sbAtPat s p).erase = p.erase
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [sbAtPat, AAtPat.erase, sbPat_erase s p1, sbPat_erase s p2, sbPatOpt_erase s p3]
  | .record r _ => by simp only [sbAtPat, AAtPat.erase, sbPatRowOpt_erase s r]
  | .paren p => by simp only [sbAtPat, AAtPat.erase, sbPat_erase s p]
theorem sbPatRowOpt_erase (s : FSub) : ∀ r : Option APatRow, APatRow.eraseOpt (sbPatRowOpt s r) = APatRow.eraseOpt r
  | none => rfl
  | some (.field _ _ rest) => by
    simp only [sbPatRowOpt, sbPatRow, APatRow.eraseOpt, APatRow.erase, sbPatRowOpt_erase s rest]
theorem sbPat_erase (s : FSub) : ∀ p : APat, (sbPat s p).erase = p.erase
  | .atpat a => by simp only [sbPat, APat.erase, sbAtPat_erase s a]
  | .con _ _ args _ => by simp only [sbPat, APat.erase, sbAtPats_erase s args]
  | .cons p1 p2 => by simp only [sbPat, APat.erase, sbPat_erase s p1, sbPat_erase s p2]
  | .as p _ => by simp only [sbPat, APat.erase, sbPat_erase s p]
theorem sbPatOpt_erase (s : FSub) : ∀ p : Option APat, APat.eraseOpt (sbPatOpt s p) = APat.eraseOpt p
  | none => rfl
  | some p => by simp only [sbPatOpt, APat.eraseOpt, sbPat_erase s p]
theorem sbAtPats_erase (s : FSub) : ∀ l : List AAtPat, AAtPat.eraseList (sbAtPats s l) = AAtPat.eraseList l
  | [] => rfl
  | a :: as => by simp only [sbAtPats, AAtPat.eraseList, sbAtPat_erase s a, sbAtPats_erase s as]
end

mutual
theorem sbAtExp_erase (s : FSub) : ∀ a : AAtExp, (sbAtExp s a).erase = a.erase
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [sbAtExp, AAtExp.erase, sbExp_erase s e1, sbExp_erase s e2, sbExpOpt_erase s e3]
  | .record r => by simp only [sbAtExp, AAtExp.erase, sbExpRowOpt_erase s r]
  | .update _ _ _ r => by simp only [sbAtExp, AAtExp.erase, sbExpRow_erase s r]
  | .letE d e => by simp only [sbAtExp, AAtExp.erase, sbDec_erase s d, sbExp_erase s e]
  | .paren e => by simp only [sbAtExp, AAtExp.erase, sbExp_erase s e]
theorem sbExpRow_erase (s : FSub) : ∀ r : AExpRow, (sbExpRow s r).erase = r.erase
  | .field _ e rest => by simp only [sbExpRow, AExpRow.erase, sbExp_erase s e, sbExpRowOpt_erase s rest]
theorem sbExpRowOpt_erase (s : FSub) : ∀ r : Option AExpRow, AExpRow.eraseOpt (sbExpRowOpt s r) = AExpRow.eraseOpt r
  | none => rfl
  | some r => by simp only [sbExpRowOpt, AExpRow.eraseOpt, sbExpRow_erase s r]
theorem sbExp_erase (s : FSub) : ∀ e : AExp, (sbExp s e).erase = e.erase
  | .atexp a => by simp only [sbExp, AExp.erase, sbAtExp_erase s a]
  | .app e a => by simp only [sbExp, AExp.erase, sbExp_erase s e, sbAtExp_erase s a]
  | .lam p e => by simp only [sbExp, AExp.erase, sbAtPat_erase s p, sbExp_erase s e]
  | .caseE e m => by simp only [sbExp, AExp.erase, sbExp_erase s e, sbMatch_erase s m]
theorem sbExpOpt_erase (s : FSub) : ∀ e : Option AExp, AExp.eraseOpt (sbExpOpt s e) = AExp.eraseOpt e
  | none => rfl
  | some e => by simp only [sbExpOpt, AExp.eraseOpt, sbExp_erase s e]
theorem sbMatch_erase (s : FSub) : ∀ m : AMatch, (sbMatch s m).erase = m.erase
  | .mk mr rest => by simp only [sbMatch, AMatch.erase, sbMRule_erase s mr, sbMatchOpt_erase s rest]
theorem sbMatchOpt_erase (s : FSub) : ∀ m : Option AMatch, AMatch.eraseOpt (sbMatchOpt s m) = AMatch.eraseOpt m
  | none => rfl
  | some m => by simp only [sbMatchOpt, AMatch.eraseOpt, sbMatch_erase s m]
theorem sbMRule_erase (s : FSub) : ∀ mr : AMRule, (sbMRule s mr).erase = mr.erase
  | .mk p e => by simp only [sbMRule, AMRule.erase, sbPat_erase s p, sbExp_erase s e]
theorem sbDec_erase (s : FSub) : ∀ d : ADec, (sbDec s d).erase = d.erase
  | .val _ vb => by simp only [sbDec, ADec.erase, sbValBind_erase s vb]
theorem sbValBind_erase (s : FSub) : ∀ vb : AValBind, (sbValBind s vb).erase = vb.erase
  | .var _ _ _ e rest => by simp only [sbValBind, AValBind.erase, sbExp_erase s e, sbValBindOpt_erase s rest]
  | .pat p e => by simp only [sbValBind, AValBind.erase, sbAtPat_erase s p, sbExp_erase s e]
theorem sbValBindOpt_erase (s : FSub) : ∀ vb : Option AValBind, AValBind.eraseOpt (sbValBindOpt s vb) = AValBind.eraseOpt vb
  | none => rfl
  | some vb => by simp only [sbValBindOpt, AValBind.eraseOpt, sbValBind_erase s vb]
end

/-! ## Completeness (section 7), up to the checker's acceptance of W's result -/

/-- What remains of `WCompleteness` (L10, soundness of W's result for the checker): on a
    successful run from the root, the checker accepts the final substitution applied to the
    annotated phrase. Proved in WSound.lean (`wResultChecks`; the derivation gives the types W records `Ty.okB`). -/
def WResultChecks : Prop :=
  ∀ fuel C0 e τ ar st, RootOK C0 →
    wExp fuel (rigidFrom (freshAbove C0)) C0 e ⟨[], freshAbove C0⟩ = .ok (τ, ar) st →
    (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
    checkExp C0 (sbExp (lk st.θ) ar) = true

/-- When a derivation exists, W's result erases to the phrase (`inferExpW`'s second check never
    fires): the image of the result is the derivation, instance lists left out. -/
theorem wExp_root_erase {fuel : Nat} {C0 : Ctx} {e : BExp} {τ : Ty} {ar : AExp} {st : WSt} (hC : RootOK C0)
    (hd : ∃ a', checkExp C0 a' = true ∧ a'.erase = e)
    (h : wExp fuel (rigidFrom (freshAbove C0)) C0 e ⟨[], freshAbove C0⟩ = .ok (τ, ar) st) :
    (sbExp (lk st.θ) ar).erase = e := by
  obtain ⟨a', hc, he⟩ := hd
  have hw := wExp_root (fuel := fuel) hC hc he
  rw [h] at hw
  obtain ⟨-, -, -, -, T, -, -, hs⟩ := hw
  have := congrArg AExp.erase hs
  rw [stripExp_erase, stripExp_erase, sbExp_erase] at this
  rw [sbExp_erase]; exact this.trans he

/-- Completeness of W (section 7) for F_c: when a derivation exists, W does not fail for any fuel,
    it does not run out from some fuel on (and then its outcome no longer changes), and it does
    not return `internal` provided the checker accepts W's result (`WResultChecks`, L10). -/
theorem wCompleteness_parts {C0 : Ctx} {e : BExp} (hC : RootOK C0)
    (hd : ∃ a', checkExp C0 a' = true ∧ a'.erase = e) :
    (∀ fuel, inferExpW fuel C0 e ≠ .fail) ∧
    (∃ n, inferExpW n C0 e ≠ .outOfFuel ∧ ∀ m, n ≤ m → inferExpW m C0 e = inferExpW n C0 e) ∧
    ∀ fuel, inferExpW fuel C0 e = .internal → ∃ τ ar st,
      wExp fuel (rigidFrom (freshAbove C0)) C0 e ⟨[], freshAbove C0⟩ = .ok (τ, ar) st ∧
      checkExp C0 (sbExp (lk st.θ) ar) = false := by
  refine ⟨fun fuel => inferExpW_ne_fail hC hd, inferExpW_terminates C0 e, fun fuel h => ?_⟩
  unfold inferExpW at h
  simp only at h
  split at h
  · rename_i τ ar st hok
    refine ⟨τ, ar, st, hok, ?_⟩
    split at h
    · cases h
    · rename_i hc
      rw [wExp_root_erase hC hd hok] at hc
      simpa using hc
  · cases h
  · cases h
  · cases h

theorem wCompleteness_of_checks (h : WResultChecks) : WCompleteness := by
  intro C0 e hC hd
  obtain ⟨h1, ⟨n, hn, -⟩, h3⟩ := wCompleteness_parts hC hd
  refine ⟨fun fuel => ⟨h1 fuel, fun hi => ?_⟩, n, hn⟩
  obtain ⟨τ, ar, st, hok, hc⟩ := h3 fuel hi
  rw [h fuel C0 e τ ar st hC hok hd] at hc
  cases hc

end StandardElm.Stat.Complete
