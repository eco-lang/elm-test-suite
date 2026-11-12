/-
  A Standard Definition of Elm? Mechanisation: W's steps in the main induction L11 of plan step 11
  (milestone (b), section 8): a fresh variable, reading the substitution, `unify` (L9 inside W:
  the state invariant is kept, every unifier absorbs the new substitution, and `unify` does not
  fail when a unifier exists), and the instantiation of a scheme.
-/
import StandardElmMech.Stat.Complete.WPhrase

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## The loop builds types W builds -/

def EqsOk (n : Nat) (E : Eqs) : Prop := ∀ e ∈ E, OkT n e.1 ∧ OkT n e.2

theorem OkT_con_args {n : Nat} {as : List Ty} {t : TyName} (h : OkT n (.con as t)) : ∀ x ∈ as, OkT n x := by
  intro x hx v hv
  exact h v (by simp only [Ty.vars]; exact uStep_next.listVars_of_mem hx hv)

theorem OkT_upd {n : Nat} {a : TyVar} {τ σ : Ty} (hτ : OkT n τ) (hσ : OkT n σ) : OkT n (sb (upd a τ) σ) :=
  OkT_sb hσ fun b hb => by
    simp only [upd]
    split
    · exact hτ
    · obtain ⟨c, e, h1, h2⟩ := hσ _ hb; injection e with e; subst e; exact OkT_var h1 h2

theorem bindStep_okT {n : Nat} {a : TyVar} {τ : Ty} {rest E' : Eqs} {θ θ' : Bnd}
    (ha : OkT n (.var a)) (hτ : OkT n τ) (hrest : EqsOk n rest) (hθ : BndOk n θ)
    (h : bindStep a τ rest θ = .next E' θ') : EqsOk n E' ∧ BndOk n θ' := by
  unfold bindStep at h
  split at h
  · split at h
    · cases h
    · cases h
      refine ⟨fun e he => ?_, fun p hp => ?_⟩
      · simp only [substEqs, List.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        exact ⟨OkT_upd hτ (hrest e0 he0).1, OkT_upd hτ (hrest e0 he0).2⟩
      · simp only [bindV, List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · obtain ⟨c, e, -, h2⟩ := ha _ (mem_vars_var a); injection e with e; subst e
          exact ⟨h2, hτ⟩
        · exact ⟨(hθ q hq).1, OkT_upd hτ (hθ q hq).2⟩
  · cases h

theorem uStep_okT {R : Rigid} {n : Nat} {θ θ' : Bnd} {l r : Ty} {rest E' : Eqs}
    (hl : OkT n l) (hr : OkT n r) (hrest : EqsOk n rest) (hθ : BndOk n θ)
    (h : uStep R θ l r rest = .next E' θ') : EqsOk n E' ∧ BndOk n θ' := by
  unfold uStep at h
  split at h
  · cases h; exact ⟨hrest, hθ⟩
  · split at h
    · split at h
      · exact bindStep_okT hl hr hrest hθ h
      · split at h
        · exact bindStep_okT hr hl hrest hθ h
        · split at h <;> cases h
    · split at h
      · exact bindStep_okT hl hr hrest hθ h
      · cases h
    · split at h
      · exact bindStep_okT hr hl hrest hθ h
      · cases h
    · cases h
      rw [OkT_fn_iff] at hl hr
      refine ⟨fun e he => ?_, hθ⟩
      simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact ⟨hl.1, hr.1⟩
      · exact ⟨hl.2, hr.2⟩
      · exact hrest e he
    · split at h
      · cases h
        refine ⟨fun e he => ?_, hθ⟩
        rcases List.mem_append.mp he with he | he
        · have hm := List.of_mem_zip he
          exact ⟨OkT_con_args hl _ hm.1, OkT_con_args hr _ hm.2⟩
        · exact hrest e he
      · cases h
    · cases h
    · cases h

theorem uLoop_okT {R : Rigid} {n : Nat} : ∀ (fuel : Nat) (E : Eqs) (θ θ' : Bnd), EqsOk n E → BndOk n θ →
    uLoop R fuel E θ = .ok θ' → BndOk n θ'
  | 0, _, _, _, _, _, h => by cases h
  | _ + 1, [], θ, θ', _, hθ, h => by simp only [uLoop, MOut.ok.injEq] at h; subst h; exact hθ
  | k + 1, (l, r) :: rest, θ, θ', hE, hθ, h => by
    simp only [uLoop] at h
    split at h
    · rename_i E1 θ1 hs
      have hl := (hE _ (.head _)).1
      have hr := (hE _ (.head _)).2
      obtain ⟨h1, h2⟩ := uStep_okT hl hr (fun e he => hE e (.tail _ he)) hθ hs
      exact uLoop_okT k E1 θ1 θ' h1 h2 h
    · cases h
    · cases h

/-! ## W's steps -/

theorem outP_freshV {β : Type} {f : Ty → WM β} {st : WSt} {P : β → WSt → Prop}
    (h : OutP P (f (.var (.fresh st.n .any)) { st with n := st.n + 1 })) : OutP P ((freshV >>= f) st) :=
  outP_bind (Q := fun a st' => a = .var (.fresh st.n .any) ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_getθ {β : Type} {f : Bnd → WM β} {st : WSt} {P : β → WSt → Prop}
    (h : OutP P (f st.θ st)) : OutP P ((getθ >>= f) st) :=
  outP_bind (Q := fun a st' => a = st.θ ∧ st' = st) ⟨rfl, rfl⟩ (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

/-- `unify` in the main induction: if `T` (fixing the rigid variables, absorbing the
    substitution) unifies the two types, `unify` does not fail, and `T` absorbs the result. -/
theorem outP_unifyW {β : Type} {fuel n0 : Nat} {τ1 τ2 : Ty} {st : WSt} {T : FSub} {f : Unit → WM β}
    {P : β → WSt → Prop} (hi : SInv n0 st) (h1 : OkT st.n τ1) (h2 : OkT st.n τ2)
    (hT : FixesR (rigidFrom n0) T) (ha : Absorbs T (lk st.θ)) (he : sb T τ1 = sb T τ2)
    (hf : ∀ st', st'.n = st.n → SInv n0 st' → Absorbs T (lk st'.θ) → OutP P (f () st')) :
    OutP P ((unifyW fuel (rigidFrom n0) τ1 τ2 >>= f) st) := by
  show OutP P (WM.bind _ f st)
  unfold WM.bind
  cases hu : unifyW fuel (rigidFrom n0) τ1 τ2 st with
  | ok u st' =>
    obtain ⟨g', hn, hc⟩ := unifyW_ok hi.good hu
    have hl : BndOk st.n st'.θ := by
      unfold unifyW at hu
      split at hu
      · rename_i θ' hloop
        simp only [WOut.ok.injEq] at hu; obtain ⟨_, rfl⟩ := hu
        refine uLoop_okT fuel _ _ _ ?_ hi.okL hloop
        intro e he
        simp only [List.mem_singleton] at he; subst he
        exact ⟨hi.ok.okT h1, hi.ok.okT h2⟩
      · cases hu
      · cases hu
      · cases hu
    exact hf st' hn ⟨by rw [hn]; exact hi.le, g', by rw [hn]; exact hl⟩ ((hc T hT).mp ⟨he, ha⟩)
  | fail => exact unifyW_fail hi.good hu T hT ha he
  | unsupported => trivial
  | outOfFuel => trivial

theorem freshFrom_okT : ∀ (k m : Nat), ∀ t ∈ freshFrom m k, OkT (m + k) t
  | 0, _, _, h => by cases h
  | k + 1, m, t, h => by
    simp only [freshFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact OkT_var rfl (isNew_fresh_lt (by omega))
    · have := freshFrom_okT k (m + 1) t h
      rw [show m + (k + 1) = m + 1 + k by omega]; exact this

theorem instVars_ne_fail : ∀ (vs : List BVar) (st : WSt), instVars vs st ≠ .fail
  | [], _, h => by cases h
  | .ty a :: vs, st, h => by
    simp only [instVars] at h
    split at h
    · simp only [bind, WM.bind, freshV] at h
      have ih := instVars_ne_fail vs { st with n := st.n + 1 }
      revert h ih
      cases instVars vs { st with n := st.n + 1 } <;> simp [pure]
    · cases h
  | .row _ :: _, _, h => by cases h

theorem instantiate_ne_fail (σ : Scheme) (st : WSt) : instantiate σ st ≠ .fail := by
  unfold instantiate
  simp only [bind, WM.bind]
  have := instVars_ne_fail σ.bound st
  revert this
  cases instVars σ.bound st with
  | ok ts st' =>
    intro _
    simp only
    cases bindSubst σ.bound ts with
    | none => simp [wUnsupported]
    | some S =>
      simp only
      cases S.apply σ.body with
      | none => simp [wUnsupported]
      | some τ => simp [pure]
  | fail => intro h; exact absurd rfl h
  | unsupported => intro _; simp
  | outOfFuel => intro _; simp

/-- W's instantiation of a scheme, in the main induction (L2). -/
theorem outP_instantiate {β : Type} {n0 : Nat} {σ : Scheme} {st : WSt} {S' : FSub} {τ' : Ty}
    {f : List Ty × Ty → WM β} {P : β → WSt → Prop}
    (hi : SInv n0 st) (hσ : SchW st.n σ) (hS : FixesR (rigidFrom n0) S') (ha : Absorbs S' (lk st.θ))
    (hinst : AnyBound σ → InstUnder S' σ τ')
    (hf : ∀ ts τ st' T, st.n ≤ st'.n → st'.θ = st.θ → SInv n0 st' → OkT st'.n τ → (∀ t ∈ ts, OkT st'.n t) →
      FixesR (rigidFrom n0) T → Absorbs T (lk st'.θ) → (∀ a, a.isNew st.n = false → T a = S' a) →
      (∀ a, T a ≠ S' a → a.cls = .any) → sb T τ = τ' → OutP P (f (ts, τ) st')) :
    OutP P ((instantiate σ >>= f) st) := by
  show OutP P (WM.bind _ f st)
  unfold WM.bind
  cases hin : instantiate σ st with
  | ok r st' =>
    obtain ⟨ts, τ⟩ := r
    obtain ⟨as, hb, hcl, hts, hτ, hθ, hn⟩ := instantiate_ok hin
    obtain ⟨T, hT1, hT2, hTc, hT3⟩ := inst_exists hσ hb (hinst ⟨as, hb, hcl⟩)
    have hle : st.n ≤ st'.n := by rw [hn]; exact Nat.le_add_right _ _
    have hi' : SInv n0 st' := ⟨Nat.le_trans hi.le hle, by rw [hθ]; exact hi.good, by
      rw [hθ]; exact hi.okL.mono hle⟩
    obtain ⟨hfx, hab⟩ := agree_ok hi.le hi.ok hS ha hT1
    subst hts hτ
    refine hf _ _ st' T hle hθ hi' (by rw [hn]; exact inst_okT hσ hb) ?_ hfx (by rw [hθ]; exact hab) hT1 hTc hT3
    intro t ht
    rw [hn]; exact freshFrom_okT _ _ t ht
  | fail => exact absurd hin (instantiate_ne_fail σ st)
  | unsupported => trivial
  | outOfFuel => trivial

end StandardElm.Stat.Complete
