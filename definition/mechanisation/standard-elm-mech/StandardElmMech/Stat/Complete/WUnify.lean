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

theorem OkT_con_args {n : Nat} {as : List Ty} {t : TyName} (h : OkT n (.con as t)) : ∀ x ∈ as, OkT n x := by
  intro x hx v hv
  exact h v (by simp only [Ty.vars]; exact uStep_next.listVars_of_mem hx hv)

theorem OkT_upd {n : Nat} {a : TyVar} {τ σ : Ty} (hτ : OkT n τ) (hσ : OkT n σ) : OkT n (sb (upd a τ) σ) :=
  OkT_sb hσ fun b hb => by
    simp only [upd]
    split
    · exact hτ
    · obtain ⟨c, e, h1, h2⟩ := hσ _ hb; injection e with e; subst e; exact OkT_var h1 h2

/-- `rigidFrom n0` gives W's invariant its flexible new variables. -/
theorem newFlex_rigidFrom {n0 n : Nat} (h : n0 ≤ n) : NewFlex (rigidFrom n0) n := fun _ ha => not_rigid_of_new h ha

theorem isBndT_of_flex {n0 : Nat} {a : TyVar} (h : rigidFrom n0 a = false) : a.isBndT = false := by
  cases a with
  | bnd _ _ => simp [rigidFrom] at h
  | _ => rfl

/-- After `unify`, the substitution binds old variables to types W builds. -/
theorem unifyW_bndOk {fuel n0 : Nat} {τ1 τ2 : Ty} {st st' : WSt} {u : Unit} (hi : SInv n0 st)
    (h1 : OkT st.n τ1) (h2 : OkT st.n τ2) (h : unifyW fuel (rigidFrom n0) τ1 τ2 st = .ok u st') :
    BndOk st'.n st'.θ := by
  unfold unifyW at h
  split at h
  · rename_i θ' n' hu
    simp only [WOut.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    have hok1 := hi.ok.okT h1
    have hok2 := hi.ok.okT h2
    have g := good_sb hi.good (fun b hb => by obtain ⟨c, e, -, h⟩ := h1 _ hb; cases e; exact h)
      (fun b hb => by obtain ⟨c, e, -, h⟩ := h2 _ hb; cases e; exact h)
    have hent := cLoop_ent (P := fun v => ∃ a, v = .ty a ∧ a.isBndT = false) fuel _ _ _ _ _ g
      (fun v hv => by
        obtain ⟨e, he, hve⟩ := mem_bvars.mp hv
        simp only [List.mem_singleton] at he; subst he
        rcases hve with hve | hve
        · obtain ⟨a, e, h, -⟩ := hok1 v hve; exact ⟨a, e, h⟩
        · obtain ⟨a, e, h, -⟩ := hok2 v hve; exact ⟨a, e, h⟩)
      (fun b hb => ⟨b, rfl, by
        cases b with
        | bnd _ _ => simp [TyVar.isNew] at hb
        | _ => rfl⟩)
      (fun p hp => ⟨⟨p.1, rfl, isBndT_of_flex (hi.good.keys p hp)⟩, fun v hv => by
        obtain ⟨a, e, h, -⟩ := (hi.okL p hp).2 v hv; exact ⟨a, e, h⟩⟩) hu
    have g' := (cLoop_ok fuel _ _ _ _ _ (newFlex_rigidFrom hi.le) g hu).1
    intro p hp
    refine ⟨(g'.oldθ p hp).1, fun v hv => ?_⟩
    obtain ⟨a, rfl, ha⟩ := (hent p hp).2 v hv
    exact ⟨a, rfl, ha, (g'.oldθ p hp).2 a hv⟩
  · cases h
  · cases h
  · cases h

/-! ## W's steps -/

theorem outP_freshV {β : Type} {f : Ty → WM β} {st : WSt} {P : β → WSt → Prop}
    (h : OutP P (f (.var (.fresh st.n .any)) { st with n := st.n + 1 })) : OutP P ((freshV >>= f) st) :=
  outP_bind (Q := fun a st' => a = .var (.fresh st.n .any) ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_freshC {β : Type} {c : Cls} {f : Ty → WM β} {st : WSt} {P : β → WSt → Prop}
    (h : OutP P (f (.var (.fresh st.n c)) { st with n := st.n + 1 })) : OutP P ((freshC c >>= f) st) :=
  outP_bind (Q := fun a st' => a = .var (.fresh st.n c) ∧ st' = { st with n := st.n + 1 }) ⟨rfl, rfl⟩
    (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

theorem outP_getθ {β : Type} {f : Bnd → WM β} {st : WSt} {P : β → WSt → Prop}
    (h : OutP P (f st.θ st)) : OutP P ((getθ >>= f) st) :=
  outP_bind (Q := fun a st' => a = st.θ ∧ st' = st) ⟨rfl, rfl⟩ (fun _ _ ⟨e1, e2⟩ => by subst e1 e2; exact h)

/-- `unify` in the main induction: if `T` (fixing the rigid variables, respecting classes,
    absorbing the substitution) unifies the two types, `unify` does not fail, and a `T'` agreeing
    with `T` on the old variables, still fixing the rigid ones and respecting classes, absorbs the
    result. -/
theorem outP_unifyW {β : Type} {fuel n0 : Nat} {τ1 τ2 : Ty} {st : WSt} {T : FSub} {f : Unit → WM β}
    {P : β → WSt → Prop} (hi : SInv n0 st) (h1 : OkT st.n τ1) (h2 : OkT st.n τ2)
    (hT : FixesR (rigidFrom n0) T) (hr : RespC T) (ha : Absorbs T (lk st.θ)) (he : sb T τ1 = sb T τ2)
    (hf : ∀ st' T', st.n ≤ st'.n → SInv n0 st' → (∀ a, a.isNew st.n = false → T' a = T a) →
      FixesR (rigidFrom n0) T' → RespC T' → Absorbs T' (lk st'.θ) → OutP P (f () st')) :
    OutP P ((unifyW fuel (rigidFrom n0) τ1 τ2 >>= f) st) := by
  have o1 : ∀ b, BVar.ty b ∈ τ1.vars → b.isNew st.n = false := fun b hb => by
    obtain ⟨c, e, -, h⟩ := h1 _ hb; cases e; exact h
  have o2 : ∀ b, BVar.ty b ∈ τ2.vars → b.isNew st.n = false := fun b hb => by
    obtain ⟨c, e, -, h⟩ := h2 _ hb; cases e; exact h
  have hN := newFlex_rigidFrom (n := st.n) hi.le
  show OutP P (WM.bind _ f st)
  unfold WM.bind
  cases hu : unifyW fuel (rigidFrom n0) τ1 τ2 st with
  | ok u st' =>
    obtain ⟨g', hn, -, hc⟩ := unifyW_ok hN hi.good o1 o2 hu
    obtain ⟨T', ag, r', ab⟩ := hc T hT hr he ha
    exact hf st' T' hn ⟨Nat.le_trans hi.le hn, g', unifyW_bndOk hi h1 h2 hu⟩ ag
      (fixesR_of_agree hN hT ag) r' ab
  | fail => exact unifyW_fail hN hi.good o1 o2 hu T hT hr ha he
  | unsupported => trivial
  | outOfFuel => trivial

theorem freshFrom_okT : ∀ (as : List TyVar) (m : Nat), ∀ t ∈ freshFrom m as, OkT (m + as.length) t
  | [], _, _, h => by cases h
  | a :: as, m, t, h => by
    simp only [freshFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact OkT_var rfl (isNew_fresh_lt (by simp))
    · have := freshFrom_okT as (m + 1) t h
      rw [show m + (a :: as).length = m + 1 + as.length by simp; omega]; exact this

theorem instVars_ne_fail : ∀ (vs : List BVar) (st : WSt), instVars vs st ≠ .fail
  | [], _, h => by cases h
  | .ty a :: vs, st, h => by
    simp only [instVars, bind, WM.bind, freshC] at h
    have ih := instVars_ne_fail vs { st with n := st.n + 1 }
    revert h ih
    cases instVars vs { st with n := st.n + 1 } <;> simp [pure]
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
    (hinst : TyBound σ → InstUnder S' σ τ')
    (hf : ∀ ts τ st' T, st.n ≤ st'.n → st'.θ = st.θ → SInv n0 st' → OkT st'.n τ → (∀ t ∈ ts, OkT st'.n t) →
      FixesR (rigidFrom n0) T → Absorbs T (lk st'.θ) → (∀ a, a.isNew st.n = false → T a = S' a) →
      (∀ a, T a ≠ S' a → Adm a.cls (T a)) → sb T τ = τ' → OutP P (f (ts, τ) st')) :
    OutP P ((instantiate σ >>= f) st) := by
  show OutP P (WM.bind _ f st)
  unfold WM.bind
  cases hin : instantiate σ st with
  | ok r st' =>
    obtain ⟨ts, τ⟩ := r
    obtain ⟨as, hb, hts, hτ, hθ, hn⟩ := instantiate_ok hin
    obtain ⟨T, hT1, hT2, hTc, hT3⟩ := inst_exists hσ hb (hinst ⟨as, hb⟩)
    have hle : st.n ≤ st'.n := by rw [hn]; exact Nat.le_add_right _ _
    have hi' : SInv n0 st' := ⟨Nat.le_trans hi.le hle, by rw [hθ]; exact hi.good.mono hle, by
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
