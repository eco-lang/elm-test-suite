/-
  A Standard Definition of Elm? Mechanisation: the statements of section 7 for W on F_d
  (milestone (d) of plan step 11), and the first lemma of their proof: a `unify` of W in its
  state (`unifyWD_ok`, `unifyWD_fail`, as WPrincipal.lean's `unifyW_ok`, `unifyW_fail` for W).

  *The derivations compared* are all those step 9's checker accepts: without free `bnd` variables
  (`NoFreeBndExp`, as for F_c) and with *canonical* types at their nodes (`CanonExp`: every row
  strictly sorted, so no label twice; `canonExp_of_checkExp`). Step 9's checker first accepted rows
  in any order and with repeated labels (milestone (a)'s finding), so a derivation could type
  `\{x} -> x` at `{x : Int, x : Bool} -> Int`; the book's rows are finite maps, and its derivations
  are exactly those whose rows are canonical lists, which the checker now asks (`Ty.okB`). Every
  equation of unification is then solvable only by canonical images (`UniR`), which is A23's
  definedness.

  The state invariant of W between unifications is `GoodR R n θ [] []` (MguR.lean's invariant with
  no pending equation and an empty frame).
-/
import StandardElmMech.Stat.Complete.WDTerm
import StandardElmMech.Stat.Complete.WPrincipal

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BExp)

/-! ## The statements (section 7, for F_d) -/

/-- The types at the nodes of a derivation are canonical. -/
def CanonExp (C : Ctx) (a : AExp) : Prop := ∀ nd ∈ nodesExp C [] a, ∀ τ ∈ nd.tys, cnB τ = true

/-- Step 9's checker asks the rows at its nodes to be canonical (`Ty.okB`): every derivation it
    accepts is canonical. -/
theorem canonExp_of_checkExp {C : Ctx} {a : AExp} (h : checkExp C a = true) : CanonExp C a :=
  fun n hn τ hτ => ((Ty.okB_iff τ).mp (okB_of_checkExp h n hn τ hτ)).1

/-- The root context is well formed for F_d: the bound variables of a scheme it binds are `bnd`
    (its canonical form) and the free ones, type or row variables, are not `bnd`. -/
def RootOKD (C0 : Ctx) : Prop :=
  ∀ lv σ st, C0.lookupVal lv = some (σ, st) →
    (∀ v ∈ σ.bound, v.isBnd = true) ∧ ∀ v ∈ σ.body.vars, v ∉ σ.bound → v.isBnd = false

theorem rootOKD_of_rootOK {C0 : Ctx} (h : RootOK C0) : RootOKD C0 := fun lv σ st hl => by
  obtain ⟨h1, h2⟩ := h lv σ st hl
  exact ⟨h1, fun v hv hb => by obtain ⟨a, rfl, ha⟩ := h2 v hv hb; exact ha⟩

/-- Refutation for F_d: if W fails, no derivation exists. -/
def WDRefutation : Prop :=
  ∀ fuel C0 e, RootOKD C0 → inferExpWD fuel C0 e = .fail →
    ¬ ∃ a', checkExp C0 a' = true ∧ a'.erase = e

/-- Completeness for F_d: if such a derivation exists, W neither fails nor returns `internal`, and
    for some fuel it does not run out. -/
def WDCompleteness : Prop :=
  ∀ C0 e, RootOKD C0 → (∃ a', checkExp C0 a' = true ∧ a'.erase = e) →
    (∀ fuel, inferExpWD fuel C0 e ≠ .fail ∧ inferExpWD fuel C0 e ≠ .internal) ∧
    ∃ fuel, inferExpWD fuel C0 e ≠ .outOfFuel

/-- Principality for F_d: what W returns is an instance-maximal derivation. -/
def WDPrincipality : Prop :=
  ∀ fuel C0 e a, RootOKD C0 → inferExpWD fuel C0 e = .ok a →
    checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true →
      a'.erase = a.erase → InstanceOfB C0 a' a

/-! ## A unification of W -/

theorem goodR_frame_nil {R : RRigid} {n : Nat} {θ : RBnd} {X : List Ty} (g : GoodR R n θ [] X) :
    GoodR R n θ [] [] :=
  goodR_of_dom g fun τ hτ => by simp [mem_tys] at hτ

/-- The variables of an image under `θ` of an old type are unbound and old. -/
theorem img_vars {R : RRigid} {n : Nat} {θ : RBnd} (g : GoodR R n θ [] []) {τ : Ty}
    (hτ : ∀ w ∈ τ.vars, newB n w = false) :
    ∀ w ∈ (rsb (toRS θ) τ).vars, (toRS θ).img w = vty w ∧ newB n w = false := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := (mem_vars_rsb _ τ w).mp hw
  refine ⟨g.idem v w hw, ?_⟩
  rw [img_toRS g.rrec] at hw
  cases hf : FMap.find? θ v with
  | none =>
    rw [hf] at hw; simp only [Option.getD_none, vars_vty, List.mem_singleton] at hw; subst hw; exact hτ w hv
  | some σ => rw [hf] at hw; exact (g.oldθ _ (rfind?_mem hf)).2 w hw

theorem goodR_unify {R : RRigid} {n : Nat} {θ : RBnd} (g : GoodR R n θ [] []) {τ1 τ2 : Ty}
    (h1 : ∀ w ∈ τ1.vars, newB n w = false) (h2 : ∀ w ∈ τ2.vars, newB n w = false)
    (c1 : cnB (rsb (toRS θ) τ1) = true) (c2 : cnB (rsb (toRS θ) τ2) = true) :
    GoodR R n θ [(rsb (toRS θ) τ1, rsb (toRS θ) τ2)] [] := by
  have hv1 := img_vars g h1
  have hv2 := img_vars g h2
  refine ⟨g.keys, g.adm, g.rrec, g.idem, fun τ hτ w hw => ?_, fun τ hτ w hw => ?_, g.oldθ, fun τ hτ => ?_⟩
  · rcases tys_cons.mp hτ with rfl | rfl | hτ
    · exact (hv1 w hw).1
    · exact (hv2 w hw).1
    · simp [mem_tys] at hτ
  · rcases tys_cons.mp hτ with rfl | rfl | hτ
    · exact (hv1 w hw).2
    · exact (hv2 w hw).2
    · simp [mem_tys] at hτ
  · rcases tys_cons.mp hτ with rfl | rfl | hτ
    · exact c1
    · exact c2
    · simp [mem_tys] at hτ

theorem absR_rsb {s : RSub} {θ : RBnd} (h : AbsR s θ) (τ : Ty) : rsb s (rsb (toRS θ) τ) = rsb s τ :=
  rsb_absorb (absR_iff.mp h) τ

/-- A `unify` of W that succeeds: the invariant is kept, every substitution absorbing the new
    accumulated substitution unifies the two types and absorbs the old one, and every unifier
    (canonical, respecting classes, fixing the rigid variables) absorbing the old one agrees on
    the old variables with one absorbing the new one. -/
theorem unifyWD_ok {fuel : Nat} {R : RRigid} {τ1 τ2 : Ty} {st st' : WDSt} {u : Unit}
    (hN : NewFlexR R st.n) (g : GoodR R st.n st.θ [] [])
    (h1 : ∀ w ∈ τ1.vars, newB st.n w = false) (h2 : ∀ w ∈ τ2.vars, newB st.n w = false)
    (c1 : cnB (rsb (toRS st.θ) τ1) = true) (c2 : cnB (rsb (toRS st.θ) τ2) = true)
    (h : unifyWD fuel R τ1 τ2 st = .ok u st') :
    GoodR R st'.n st'.θ [] [] ∧ st.n ≤ st'.n ∧
      (∀ s, AbsR s st'.θ → rsb s τ1 = rsb s τ2 ∧ AbsR s st.θ) ∧
      (∀ s, FixR R s → RespR s → rsb s τ1 = rsb s τ2 → cnB (rsb s τ1) = true → AbsR s st.θ →
        ∃ s', (∀ v, newB st.n v = false → s'.img v = s.img v) ∧ RespR s' ∧ AbsR s' st'.θ) := by
  unfold unifyWD at h
  split at h
  · rename_i θ' n' hu
    simp only [WDOut.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    obtain ⟨X', g', hn, c⟩ := rLoop_ok fuel _ _ _ _ _ _ hN (goodR_unify g h1 h2 c1 c2) hu
    have hself : AbsR (toRS θ') θ' := fun v => rsb_eq_self fun w hw => g'.idem v w hw
    have hu0 : UniR (toRS θ') [] X' := by
      refine ⟨fun _ h => absurd h List.not_mem_nil, fun τ hτ => ?_⟩
      rw [rsb_eq_self fun w hw => g'.stable τ hτ w hw]; exact g'.cn τ hτ
    obtain ⟨⟨he, _⟩, hab⟩ := c.1 _ hu0 hself
    have heq : rsb (toRS θ') (rsb (toRS st.θ) τ1) = rsb (toRS θ') (rsb (toRS st.θ) τ2) := he _ (List.mem_singleton_self _)
    rw [absR_rsb hab, absR_rsb hab] at heq
    refine ⟨goodR_frame_nil g', hn, fun s hs => ?_, fun s hs hr he' hc ha => ?_⟩
    · have hθ : rcomp s (toRS θ') = s := absR_iff.mp hs
      refine ⟨?_, ?_⟩
      · rw [← rsb_absorb hθ τ1, ← rsb_absorb hθ τ2, heq]
      · apply absR_iff.mpr
        rw [← hθ, ← rcomp_assoc, absR_iff.mp hab]
    · obtain ⟨s', ag, r', _, ab⟩ := c.2 s hs hr ⟨fun e he => by
          rcases List.mem_singleton.mp he with rfl
          simp only [absR_rsb ha]; exact he', fun τ hτ => by
          rcases tys_cons.mp hτ with rfl | rfl | hτ
          · rw [absR_rsb ha]; exact hc
          · rw [absR_rsb ha, ← he']; exact hc
          · simp [mem_tys] at hτ⟩ ha
      exact ⟨s', ag, r', ab⟩
  · cases h
  · cases h

/-- A `unify` of W that fails: no unifier absorbing the accumulated substitution. -/
theorem unifyWD_fail {fuel : Nat} {R : RRigid} {τ1 τ2 : Ty} {st : WDSt}
    (hN : NewFlexR R st.n) (g : GoodR R st.n st.θ [] [])
    (h1 : ∀ w ∈ τ1.vars, newB st.n w = false) (h2 : ∀ w ∈ τ2.vars, newB st.n w = false)
    (h : unifyWD fuel R τ1 τ2 st = .fail) :
    ∀ s, FixR R s → RespR s → AbsR s st.θ → rsb s τ1 = rsb s τ2 → cnB (rsb s τ1) = true → False := by
  unfold unifyWD at h
  split at h
  · cases h
  · rename_i hu
    intro s hs hr ha he hc
    have c1 : cnB (rsb (toRS st.θ) τ1) = true := cnB_of_rsb (s := s) (by rw [absR_rsb ha]; exact hc)
    have c2 : cnB (rsb (toRS st.θ) τ2) = true := cnB_of_rsb (s := s) (by rw [absR_rsb ha, ← he]; exact hc)
    apply rLoop_fail fuel _ _ _ _ hN (goodR_unify g h1 h2 c1 c2) hu s hs hr _ ha
    refine ⟨fun e he' => ?_, fun τ hτ => ?_⟩
    · rcases List.mem_singleton.mp he' with rfl
      simp only [absR_rsb ha]; exact he
    · rcases tys_cons.mp hτ with rfl | rfl | hτ
      · rw [absR_rsb ha]; exact hc
      · rw [absR_rsb ha, ← he]; exact hc
      · simp [mem_tys] at hτ
  · cases h

end StandardElm.Stat.Complete
