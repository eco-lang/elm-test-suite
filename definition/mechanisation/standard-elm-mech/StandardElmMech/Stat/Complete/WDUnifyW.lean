/-
  A Standard Definition of Elm? Mechanisation: W's steps in the main induction L11 with rows
  (plan step 11, milestone (d), section 8; WUnify.lean for `inferExpWD`): a fresh variable (type
  or row), reading the substitution, `unify` (L9 inside W, with canonical images: the state
  invariant is kept, every unifier absorbs the new substitution, and `unify` does not fail when a
  unifier with a canonical image exists), and the instantiation of a scheme.
-/
import StandardElmMech.Stat.Complete.WDPhrase

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

theorem OkT_con_argsD {n : Nat} {as : List Ty} {t : TyName} (h : OkTD n (.con as t)) : ∀ x ∈ as, OkTD n x := by
  intro x hx v hv
  exact h v (by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨x, hx, hv⟩)

/-! ## W's steps -/

theorem outP_freshVD {β : Type} {f : Ty → WDM β} {st : WDSt} {P : β → WDSt → Prop}
    (h : OutPD P (f (.var (.fresh st.n .any)) { st with n := st.n + 1 })) : OutPD P ((freshVD >>= f) st) :=
  outP_bindD (Q := fun a st' => a = .var (.fresh st.n .any) ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_freshCD {β : Type} {c : Cls} {f : Ty → WDM β} {st : WDSt} {P : β → WDSt → Prop}
    (h : OutPD P (f (.var (.fresh st.n c)) { st with n := st.n + 1 })) : OutPD P ((freshCD c >>= f) st) :=
  outP_bindD (Q := fun a st' => a = .var (.fresh st.n c) ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_freshRowD {β : Type} {f : RowVar → WDM β} {st : WDSt} {P : β → WDSt → Prop}
    (h : OutPD P (f (.fresh st.n) { st with n := st.n + 1 })) : OutPD P ((freshRowD >>= f) st) :=
  outP_bindD (Q := fun a st' => a = .fresh st.n ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_getθD {β : Type} {f : RBnd → WDM β} {st : WDSt} {P : β → WDSt → Prop}
    (h : OutPD P (f st.θ st)) : OutPD P ((getθD >>= f) st) :=
  outP_bindD (Q := fun a st' => a = st.θ ∧ st' = st) ⟨rfl, rfl⟩ (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

/-- `unify` in the main induction: if `T` (fixing the rigid variables, respecting classes,
    absorbing the substitution) unifies the two types with a canonical image, `unify` does not
    fail, and a `T'` agreeing with `T` on the old variables, still fixing the rigid ones and
    respecting classes, absorbs the result. -/
theorem outP_unifyWD {β : Type} {fuel n0 : Nat} {τ1 τ2 : Ty} {st : WDSt} {T : RSub} {f : Unit → WDM β}
    {P : β → WDSt → Prop} (hi : SInvD n0 st) (h1 : OkTD st.n τ1) (h2 : OkTD st.n τ2)
    (hT : FixR (rigidFromD n0) T) (hr : RespR T) (ha : AbsR T st.θ) (he : rsb T τ1 = rsb T τ2)
    (hc : cnB (rsb T τ1) = true)
    (hf : ∀ st' T', st.n ≤ st'.n → SInvD n0 st' → (∀ v, newB st.n v = false → T'.img v = T.img v) →
      FixR (rigidFromD n0) T' → RespR T' → AbsR T' st'.θ → OutPD P (f () st')) :
    OutPD P ((unifyWD fuel (rigidFromD n0) τ1 τ2 >>= f) st) := by
  have hN := newFlexR_rigidFromD (n := st.n) hi.le
  have c1 : cnB (rsb (toRS st.θ) τ1) = true := cnB_of_rsb (s := T) (by rw [absR_rsb ha]; exact hc)
  have c2 : cnB (rsb (toRS st.θ) τ2) = true := cnB_of_rsb (s := T) (by rw [absR_rsb ha, ← he]; exact hc)
  show OutPD P (WDM.bind _ f st)
  unfold WDM.bind
  cases hu : unifyWD fuel (rigidFromD n0) τ1 τ2 st with
  | ok u st' =>
    obtain ⟨g', hn, -, hcc⟩ := unifyWD_ok hN hi.good h1.old h2.old c1 c2 hu
    obtain ⟨T', ag, r', ab⟩ := hcc T hT hr he hc ha
    exact hf st' T' hn ⟨Nat.le_trans hi.le hn, g'⟩ ag (fixR_of_agree hN hT ag) r' ab
  | fail => exact unifyWD_fail hN hi.good h1.old h2.old hu T hT hr ha he hc
  | unsupported => trivial
  | outOfFuel => trivial

theorem instVarsD_ne_fail : ∀ (vs : List BVar) (st : WDSt), instVarsD vs st ≠ .fail
  | [], _, h => by cases h
  | .ty a :: vs, st, h => by
    simp only [instVarsD, bind, WDM.bind, freshCD] at h
    have ih := instVarsD_ne_fail vs { st with n := st.n + 1 }
    revert h ih
    cases instVarsD vs { st with n := st.n + 1 } <;> simp [pure]
  | .row _ :: vs, st, h => by
    simp only [instVarsD, bind, WDM.bind, freshRowD] at h
    have ih := instVarsD_ne_fail vs { st with n := st.n + 1 }
    revert h ih
    cases instVarsD vs { st with n := st.n + 1 } <;> simp [pure]

theorem instantiateD_ne_fail (σ : Scheme) (st : WDSt) : instantiateD σ st ≠ .fail := by
  unfold instantiateD
  simp only [bind, WDM.bind]
  have := instVarsD_ne_fail σ.bound st
  revert this
  cases instVarsD σ.bound st with
  | ok ts st' =>
    intro _
    simp only
    cases bindSubst σ.bound ts with
    | none => simp [wdUnsupported]
    | some S =>
      simp only
      cases S.apply σ.body with
      | none => simp [wdUnsupported]
      | some τ => simp [pure]
  | fail => intro h; exact absurd rfl h
  | unsupported => intro _; simp
  | outOfFuel => intro _; simp

/-- W's instantiation of a scheme, in the main induction (L2). -/
theorem outP_instantiateD {β : Type} {n0 : Nat} {σ : Scheme} {st : WDSt} {S' : RSub} {τ' : Ty}
    {f : List Ty × Ty → WDM β} {P : β → WDSt → Prop}
    (hi : SInvD n0 st) (hσ : SchWD st.n σ) (hS : FixR (rigidFromD n0) S') (ha : AbsR S' st.θ)
    (hinst : InstUnderD S' σ τ')
    (hf : ∀ ts τ st' T, st.n ≤ st'.n → st'.θ = st.θ → SInvD n0 st' → OkTD st'.n τ → (∀ t ∈ ts, OkTD st'.n t) →
      FixR (rigidFromD n0) T → AbsR T st'.θ → (∀ v, newB st.n v = false → T.img v = S'.img v) →
      (∀ a, T.t a ≠ S'.t a → Adm a.cls (T.t a)) → rsb T τ = τ' → OutPD P (f (ts, τ) st')) :
    OutPD P ((instantiateD σ >>= f) st) := by
  show OutPD P (WDM.bind _ f st)
  unfold WDM.bind
  cases hin : instantiateD σ st with
  | ok r st' =>
    obtain ⟨ts, τ⟩ := r
    obtain ⟨hts, hτ, hθ, hn⟩ := instantiateD_ok hin
    obtain ⟨T, hT1, -, hTc, hT3⟩ := inst_existsD hσ hinst
    have hle : st.n ≤ st'.n := by rw [hn]; exact Nat.le_add_right _ _
    have hi' : SInvD n0 st' := ⟨Nat.le_trans hi.le hle, by rw [hθ]; exact goodR_mono hi.good hle⟩
    obtain ⟨hfx, hab⟩ := agree_okD hi.le hi.good hS ha hT1
    subst hts hτ
    refine hf _ _ st' T hle hθ hi' (by rw [hn]; exact inst_okTD hσ) ?_ hfx (by rw [hθ]; exact hab) hT1 hTc hT3
    intro t ht
    rw [hn]; exact freshFromD_okT _ _ t ht
  | fail => exact absurd hin (instantiateD_ne_fail σ st)
  | unsupported => trivial
  | outOfFuel => trivial

end StandardElm.Stat.Complete
