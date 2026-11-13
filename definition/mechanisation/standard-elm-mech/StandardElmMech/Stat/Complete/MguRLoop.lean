/-
  A Standard Definition of Elm? Mechanisation: unification with rows, the loop and the mgu
  theorem (plan step 11, section 4, parts 1 and 2), milestone (d).

  * `uStepR_next`, `uStepR_fail`: one step keeps the invariant (I1) and the solution
    correspondence (I2); a failing step has no unifier (I3). The cases other than records are
    those of MguC.lean with substitutions of type and row variables; the record case is
    MguRStep.lean.
  * `rLoop_ok`, `rLoop_fail`, and the mgu theorem `mguR_ok` (the result unifies the problem, is
    canonical on it, fixes the rigid variables, respects classes, is idempotent, and every unifier
    factors through it, by a substitution agreeing with it on the old variables) and `mguR_fail`
    (no unifier). Termination is MguRTerm.lean.
-/
import StandardElmMech.Stat.Complete.MguRStep

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

theorem uniR_cons_l {s : RSub} {l r : Ty} {E : Eqs} {X : List Ty} :
    UniR s ((l, r) :: E) X ↔ rsb s l = rsb s r ∧ UniR s E (l :: X) := by
  rw [uniR_cons]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h1 ▸ uniR_frame h2⟩

theorem uniR_cons_r {s : RSub} {l r : Ty} {E : Eqs} {X : List Ty} :
    UniR s ((l, r) :: E) X ↔ rsb s l = rsb s r ∧ UniR s E (r :: X) := by
  rw [uniR_cons]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun τ hτ => ?_⟩
    rcases tys_frame_cons.mp hτ with rfl | hτ
    · exact h4
    · exact h3 τ (tys_frame_cons.mpr (.inr hτ))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ⟨h2, fun τ hτ => ?_⟩, uniR_frame ⟨h2, h3⟩⟩
    rcases tys_frame_cons.mp hτ with rfl | hτ
    · rw [h1]; exact uniR_frame ⟨h2, h3⟩
    · exact h3 τ (tys_frame_cons.mpr (.inr hτ))

theorem tys_head_l {l r : Ty} {E : Eqs} {X : List Ty} : l ∈ tys ((l, r) :: E) X := tys_cons.mpr (.inl rfl)
theorem tys_head_r {l r : Ty} {E : Eqs} {X : List Ty} : r ∈ tys ((l, r) :: E) X := tys_cons.mpr (.inr (.inl rfl))

theorem tys_sub_l {l r : Ty} {E : Eqs} {X : List Ty} : ∀ σ ∈ tys E (l :: X), σ ∈ tys ((l, r) :: E) X := by
  intro σ hσ
  rcases tys_frame_cons.mp hσ with rfl | hσ
  · exact tys_head_l
  · exact tys_cons.mpr (.inr (.inr hσ))

theorem tys_sub_r {l r : Ty} {E : Eqs} {X : List Ty} : ∀ σ ∈ tys E (r :: X), σ ∈ tys ((l, r) :: E) X := by
  intro σ hσ
  rcases tys_frame_cons.mp hσ with rfl | hσ
  · exact tys_head_r
  · exact tys_cons.mpr (.inr (.inr hσ))

/-! ## Type-variable bindings at the head -/

section var
variable {R : RRigid} {n : Nat} {θ : RBnd} {rest : Eqs} {X : List Ty}

/-- `var a ≐ τ` bound as `a ↦ τ`. -/
theorem bindL_case {a : TyVar} {τ : Ty} (hR : R (.ty a) = false) (hadm : Adm a.cls τ) (hocc : BVar.ty a ∉ τ.vars)
    (g : GoodR R n θ ((.var a, τ) :: rest) X) :
    GoodR R n (bindR (.ty a) τ θ) (sE (one (.ty a) τ) rest) (sX (one (.ty a) τ) (.var a :: X)) ∧
      CorrR R n ((.var a, τ) :: rest) X θ (sE (one (.ty a) τ) rest) (sX (one (.ty a) τ) (.var a :: X)) (bindR (.ty a) τ θ) :=
  bindR_case hR trivial (fun b e => by cases e; exact hadm) hocc (fun e h => by cases h) g
    (fun s => uniR_cons_l) tys_sub_l tys_head_r tys_head_l

/-- `l ≐ var b` bound as `b ↦ l`. -/
theorem bindRt_case {b : TyVar} {l : Ty} (hR : R (.ty b) = false) (hadm : Adm b.cls l) (hocc : BVar.ty b ∉ l.vars)
    (g : GoodR R n θ ((l, .var b) :: rest) X) :
    GoodR R n (bindR (.ty b) l θ) (sE (one (.ty b) l) rest) (sX (one (.ty b) l) (.var b :: X)) ∧
      CorrR R n ((l, .var b) :: rest) X θ (sE (one (.ty b) l) rest) (sX (one (.ty b) l) (.var b :: X)) (bindR (.ty b) l θ) :=
  bindR_case hR trivial (fun c e => by cases e; exact hadm) hocc (fun e h => by cases h) g
    (fun s => by rw [uniR_cons_r]; exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩)
    tys_sub_r tys_head_l tys_head_r

/-- `var a ≐ var b` bound as `b ↦ a`, the left side `var a` in the frame. -/
theorem bindLb_case {a b : TyVar} (hR : R (.ty b) = false) (hadm : Adm b.cls (.var a)) (hocc : BVar.ty b ∉ (Ty.var a).vars)
    (g : GoodR R n θ ((.var a, .var b) :: rest) X) :
    GoodR R n (bindR (.ty b) (.var a) θ) (sE (one (.ty b) (.var a)) rest) (sX (one (.ty b) (.var a)) (.var a :: X)) ∧
      CorrR R n ((.var a, .var b) :: rest) X θ (sE (one (.ty b) (.var a)) rest) (sX (one (.ty b) (.var a)) (.var a :: X))
        (bindR (.ty b) (.var a) θ) :=
  bindR_case hR trivial (fun c e => by cases e; exact hadm) hocc (fun e h => by cases h) g
    (fun s => by rw [uniR_cons_l]; exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩)
    tys_sub_l tys_head_l tys_head_r

theorem varStepR_next {a : TyVar} {τ : Ty} {cur : Eqs} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ cur X) (hcur : ∀ s, UniR s cur X → s.t a = rsb s τ)
    (hτc : ∀ w ∈ τ.vars, (toRS θ).img w = vty w ∧ newB n w = false)
    (gb : ∀ (_ : Adm a.cls τ) (_ : BVar.ty a ∉ τ.vars),
      GoodR R n (bindR (.ty a) τ θ) (sE (one (.ty a) τ) rest) (sX (one (.ty a) τ) (.var a :: X)) ∧
      CorrR R n cur X θ (sE (one (.ty a) τ) rest) (sX (one (.ty a) τ) (.var a :: X)) (bindR (.ty a) τ θ))
    (h : varStepR R a τ cur rest X θ n = .next E' X' θ' n') :
    GoodR R n' θ' E' X' ∧ n ≤ n' ∧ CorrR R n cur X θ E' X' θ' := by
  unfold varStepR at h
  split at h
  · cases h
  · rename_i hocc
    split at h
    · cases h
    · rename_i ps hps
      split at h
      · cases h
      · simp only [bindS, RStep.next.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hadm := adm_of_req hps (refineTarget_all (by assumption))
        exact ⟨(gb hadm hocc).1, Nat.le_refl _, (gb hadm hocc).2⟩
      · rename_i b m ht
        simp only [refineS, bindS, RStep.next.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨k, hk, hRb, hm, hle⟩ := refineTarget_some ht
        have hbτ : BVar.ty b ∈ τ.vars := reqC_vars _ _ _ hps _ hk
        obtain ⟨g', c⟩ := refineR_case hRb (meet_lt hm hle).1 g (hτc _ hbτ).1 (hτc _ hbτ).2 (by
          intro s _ hr hu
          have e := hcur s hu
          have h1 : Adm a.cls (rsb s τ) := e ▸ hr a
          have h2 := (reqC_specR s _ _ _ hps).mp h1 _ hk
          obtain ⟨m', hm', hadm⟩ := admC_meet (hr b) h2
          rw [hm] at hm'; cases hm'; exact hadm)
        exact ⟨g', Nat.le_succ n, c⟩

theorem varStepR_fail {a : TyVar} {τ : Ty} {cur : Eqs} (hτ : ∀ b, τ ≠ .var b)
    (h : varStepR R a τ cur rest X θ n = .fail) : ∀ s, FixR R s → RespR s → s.t a ≠ rsb s τ := by
  intro s hs hr e
  unfold varStepR at h
  split at h
  · rename_i hocc; exact occurs_neR s hocc (hτ a) e
  · split at h
    · rename_i hreq; exact reqC_noneR s _ _ hreq (e ▸ hr a)
    · rename_i ps hps
      split at h
      · rename_i ht
        obtain ⟨⟨b, k⟩, hp, hle, hor⟩ := refineTarget_none ht
        have hk : Adm k (s.t b) := (reqC_specR s _ _ _ hps).mp (e ▸ hr a) _ hp
        rcases hor with hrb | hm
        · have := hs (.ty b) hrb; simp only [RSub.img, vty] at this; rw [this] at hk
          simp only at hle; rw [admC_var_iff.mp hk] at hle; cases hle
        · exact admC_meet_none hm (hr b) hk
      · simp [bindS] at h
      · simp [refineS, bindS] at h

end var

/-! ## One step -/

theorem fn_dom {a b c d : Ty} {rest : Eqs} {X : List Ty} :
    ∀ τ ∈ tys ((a, c) :: (b, d) :: rest) X, ∃ σ ∈ tys ((.fn a b, .fn c d) :: rest) X,
      (∀ w ∈ τ.vars, w ∈ σ.vars) ∧ (cnB σ = true → cnB τ = true) := by
  intro τ hτ
  rcases tys_cons.mp hτ with rfl | rfl | hτ
  · exact ⟨_, tys_head_l, fun w hw => by simp [Ty.vars, hw], fun h => by simp only [cnB, Bool.and_eq_true] at h; exact h.1⟩
  · exact ⟨_, tys_head_r, fun w hw => by simp [Ty.vars, hw], fun h => by simp only [cnB, Bool.and_eq_true] at h; exact h.1⟩
  rcases tys_cons.mp hτ with rfl | rfl | hτ
  · exact ⟨_, tys_head_l, fun w hw => by simp [Ty.vars, hw], fun h => by simp only [cnB, Bool.and_eq_true] at h; exact h.2⟩
  · exact ⟨_, tys_head_r, fun w hw => by simp [Ty.vars, hw], fun h => by simp only [cnB, Bool.and_eq_true] at h; exact h.2⟩
  · exact ⟨τ, tys_cons.mpr (.inr (.inr hτ)), fun _ h => h, id⟩

theorem con_dom {as bs : List Ty} {t : TyName} {rest : Eqs} {X : List Ty} :
    ∀ τ ∈ tys (as.zip bs ++ rest) X, ∃ σ ∈ tys ((.con as t, .con bs t) :: rest) X,
      (∀ w ∈ τ.vars, w ∈ σ.vars) ∧ (cnB σ = true → cnB τ = true) := by
  intro τ hτ
  rcases tys_append.mp hτ with hτ | ⟨e, he, hτe⟩
  · exact ⟨τ, tys_cons.mpr (.inr (.inr hτ)), fun _ h => h, id⟩
  · have hm := List.of_mem_zip he
    rcases hτe with rfl | rfl
    · exact ⟨_, tys_head_l, fun w hw => by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨_, hm.1, hw⟩,
        fun h => by simp only [cnB, cnListB_iff] at h; exact h _ hm.1⟩
    · exact ⟨_, tys_head_r, fun w hw => by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨_, hm.2, hw⟩,
        fun h => by simp only [cnB, cnListB_iff] at h; exact h _ hm.2⟩

theorem mem_zip_left {x : Ty} : ∀ {as bs : List Ty}, as.length = bs.length → x ∈ as → ∃ y, (x, y) ∈ as.zip bs
  | [], _, _, hx => nomatch hx
  | a :: as, b :: bs, h, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_left h hx; exact ⟨y, List.mem_cons_of_mem _ hy⟩
  | _ :: _, [], h, _ => by cases h

theorem rsbList_inj_zip {s : RSub} : ∀ {as bs : List Ty}, as.length = bs.length →
    (rsbList s as = rsbList s bs ↔ ∀ e ∈ as.zip bs, rsb s e.1 = rsb s e.2)
  | [], [], _ => by simp [rsbList]
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [rsbList, List.cons.injEq, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp, rsbList_inj_zip h]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem uStepR_next {R : RRigid} {n : Nat} {θ : RBnd} {l r : Ty} {rest : Eqs} {X : List Ty}
    {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ ((l, r) :: rest) X) (h : uStepR R θ n l r rest X = .next E' X' θ' n') :
    GoodR R n' θ' E' X' ∧ n ≤ n' ∧ CorrR R n ((l, r) :: rest) X θ E' X' θ' := by
  have hl : ∀ w ∈ l.vars, (toRS θ).img w = vty w ∧ newB n w = false :=
    fun w hw => ⟨g.stable _ tys_head_l w hw, g.old _ tys_head_l w hw⟩
  have hr : ∀ w ∈ r.vars, (toRS θ).img w = vty w ∧ newB n w = false :=
    fun w hw => ⟨g.stable _ tys_head_r w hw, g.old _ tys_head_r w hw⟩
  unfold uStepR at h
  split at h
  · rename_i hlr
    cases h; subst hlr
    refine ⟨goodR_tail g, Nat.le_refl _, fun s h1 h2 => ⟨uniR_cons_l.mpr ⟨rfl, h1⟩, h2⟩,
      fun s _ hr' h1 h2 => ⟨s, fun _ _ => rfl, hr', (uniR_cons_l.mp h1).2, h2⟩⟩
  · split at h
    · -- var, var
      rename_i a b hab
      have hab' : a ≠ b := fun e => hab (by rw [e])
      have nab : BVar.ty a ∉ (Ty.var b).vars := by simpa [Ty.vars] using hab'
      have nba : BVar.ty b ∉ (Ty.var a).vars := by simpa [Ty.vars] using fun e => hab' e.symm
      split at h
      · rename_i hfl
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfl
        split at h
        · cases h
        · rename_i m hm
          obtain ⟨hma, hmb, _⟩ := (Cls.meet_spec _ _ m).mp hm
          split at h
          · rename_i e; subst e
            simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨g', c⟩ := bindL_case hfl.1 (admC_var_iff.mpr hma) nab g
            exact ⟨g', Nat.le_refl _, c⟩
          · split at h
            · rename_i _ e; subst e
              simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              obtain ⟨g', c⟩ := bindLb_case hfl.2 (admC_var_iff.mpr hmb) nba g
              exact ⟨g', Nat.le_refl _, c⟩
            · simp only [refineS, bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              obtain ⟨g', c⟩ := refineR_case hfl.1 hma g (hl _ (mem_vars_var a)).1 (hl _ (mem_vars_var a)).2
                (by
                  intro s _ hr' hu
                  have e : s.t a = s.t b := (uniR_cons_l.mp hu).1
                  obtain ⟨m', hm', hadm⟩ := admC_meet (hr' a) (e ▸ hr' b)
                  rw [hm] at hm'; cases hm'; exact hadm)
              exact ⟨g', Nat.le_succ n, c⟩
      · split at h
        · rename_i hra
          simp only [Bool.not_eq_true'] at hra
          split at h
          · rename_i hle
            simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨g', c⟩ := bindL_case hra (admC_var_iff.mpr hle) nab g
            exact ⟨g', Nat.le_refl _, c⟩
          · cases h
        · split at h
          · rename_i _ hrb
            simp only [Bool.not_eq_true'] at hrb
            split at h
            · rename_i hle
              simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              obtain ⟨g', c⟩ := bindLb_case hrb (admC_var_iff.mpr hle) nba g
              exact ⟨g', Nat.le_refl _, c⟩
            · cases h
          · cases h
    · -- var, non-var
      rename_i a r' _ _
      split at h
      · rename_i hra
        simp only [Bool.not_eq_true'] at hra
        exact varStepR_next g (fun s hu => (uniR_cons_l.mp hu).1) hr
          (fun ha hocc => bindL_case hra ha hocc g) h
      · cases h
    · -- non-var, var
      rename_i l' b _ _
      split at h
      · rename_i hrb
        simp only [Bool.not_eq_true'] at hrb
        exact varStepR_next g (fun s hu => (uniR_cons_l.mp hu).1.symm) hl
          (fun ha hocc => bindRt_case hrb ha hocc g) h
      · cases h
    · -- fn, fn
      cases h
      refine ⟨goodR_of_dom g fn_dom, Nat.le_refl _, fun s h1 h2 => ⟨?_, h2⟩, fun s _ hr' h1 h2 => ⟨s, fun _ _ => rfl, hr', ?_, h2⟩⟩
      · obtain ⟨e1, e2⟩ := h1
        refine uniR_cons_l.mpr ⟨?_, ⟨fun e he => e1 e (.tail _ (.tail _ he)), fun τ hτ => ?_⟩⟩
        · simp only [rsb, Ty.fn.injEq]; exact ⟨e1 _ (.head _), e1 _ (.tail _ (.head _))⟩
        · rcases tys_frame_cons.mp hτ with rfl | hτ
          · simp only [rsb, cnB, Bool.and_eq_true]
            exact ⟨e2 _ (tys_cons.mpr (.inl rfl)), e2 _ (tys_cons.mpr (.inr (.inr (tys_cons.mpr (.inl rfl)))))⟩
          · exact e2 τ (tys_cons.mpr (.inr (.inr (tys_cons.mpr (.inr (.inr hτ))))))
      · obtain ⟨e1, e2⟩ := uniR_cons_l.mp h1
        simp only [rsb, Ty.fn.injEq] at e1
        have cl := uniR_frame e2
        have cr := (uniR_cons.mp h1).2.2
        simp only [rsb, cnB, Bool.and_eq_true] at cl cr
        refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact e1.1
          rcases List.mem_cons.mp he with rfl | he
          · exact e1.2
          · exact e2.1 e he
        · rcases tys_cons.mp hτ with rfl | rfl | hτ
          · exact cl.1
          · exact cr.1
          rcases tys_cons.mp hτ with rfl | rfl | hτ
          · exact cl.2
          · exact cr.2
          · exact e2.2 τ (tys_frame_cons.mpr (.inr hτ))
    · -- con, con
      split at h
      · rename_i as t bs t' hc
        obtain ⟨rfl, hlen⟩ := hc
        cases h
        refine ⟨goodR_of_dom g con_dom, Nat.le_refl _, fun s h1 h2 => ⟨?_, h2⟩, fun s _ hr' h1 h2 => ⟨s, fun _ _ => rfl, hr', ?_, h2⟩⟩
        · obtain ⟨e1, e2⟩ := h1
          refine uniR_cons_l.mpr ⟨?_, ⟨fun e he => e1 e (List.mem_append_right _ he), fun τ hτ => ?_⟩⟩
          · simp only [rsb, Ty.con.injEq, and_true]
            exact (rsbList_inj_zip hlen).mpr fun e he => e1 e (List.mem_append_left _ he)
          · rcases tys_frame_cons.mp hτ with rfl | hτ
            · simp only [rsb, cnB, rsbList_eq, cnListB_iff, List.mem_map]
              rintro _ ⟨x, hx, rfl⟩
              obtain ⟨y, hy⟩ := mem_zip_left hlen hx
              exact e2 x (tys_append.mpr (.inr ⟨(x, y), hy, .inl rfl⟩))
            · exact e2 τ (tys_append.mpr (.inl hτ))
        · obtain ⟨e1, e2⟩ := uniR_cons_l.mp h1
          simp only [rsb, Ty.con.injEq, and_true] at e1
          have cl := uniR_frame e2
          have cr := (uniR_cons.mp h1).2.2
          simp only [rsb, cnB, rsbList_eq, cnListB_iff, List.mem_map] at cl cr
          refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
          · rcases List.mem_append.mp he with he | he
            · exact (rsbList_inj_zip hlen).mp e1 e he
            · exact e2.1 e he
          · rcases tys_append.mp hτ with hτ | ⟨e, he, hτe⟩
            · exact e2.2 τ (tys_frame_cons.mpr (.inr hτ))
            · have hm := List.of_mem_zip he
              rcases hτe with rfl | rfl
              · exact cl _ ⟨_, hm.1, rfl⟩
              · exact cr _ ⟨_, hm.2, rfl⟩
      · cases h
    · -- record, record
      exact recStep_next g h
    · cases h

theorem uStepR_fail {R : RRigid} {n : Nat} {θ : RBnd} {l r : Ty} {rest : Eqs} {X : List Ty}
    (g : GoodR R n θ ((l, r) :: rest) X) (h : uStepR R θ n l r rest X = .fail) :
    ∀ s, FixR R s → RespR s → UniR s ((l, r) :: rest) X → False := by
  intro s hs hr hu
  have heq := (uniR_cons_l.mp hu).1
  have fixT : ∀ a, R (.ty a) = true → s.t a = .var a := fun a h => hs (.ty a) h
  revert heq
  unfold uStepR at h
  by_cases hlr : l = r
  · simp only [hlr, ↓reduceIte] at h; cases h
  simp only [hlr, ↓reduceIte] at h
  match l, r, h, hlr, g, hu with
  | .var a, .var b, h, hlr, _, _ =>
    dsimp only at h
    have hab : a ≠ b := fun e => hlr (by rw [e])
    simp only [rsb]
    split at h
    · split at h
      · rename_i hm; intro e; exact admC_meet_none hm (hr a) (e ▸ hr b)
      · split at h
        · simp [bindS] at h
        · split at h
          · simp [bindS] at h
          · simp [refineS, bindS] at h
    · rename_i hfl
      split at h
      · rename_i hra
        simp only [Bool.not_eq_true'] at hra
        have hrb : R (.ty b) = true := by
          cases hb : R (.ty b)
          · simp [hra, hb] at hfl
          · rfl
        split at h
        · simp [bindS] at h
        · rename_i hle
          intro e; rw [fixT b hrb] at e
          exact hle (admC_var_iff.mp (e ▸ hr a))
      · rename_i hra
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
        split at h
        · rename_i hrb
          simp only [Bool.not_eq_true'] at hrb
          split at h
          · simp [bindS] at h
          · rename_i hle
            intro e; rw [fixT a hra] at e
            exact hle (admC_var_iff.mp (e.symm ▸ hr b))
        · rename_i hrb
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
          rw [fixT a hra, fixT b hrb]
          intro e; injection e with e; exact hab e
  | .var a, .record ρ tl, h, _, _, _ =>
    dsimp only at h; split at h
    · exact varStepR_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      intro e; simp only [rsb] at e; rw [fixT a hra] at e; cases e
  | .var a, .fn x y, h, _, _, _ =>
    dsimp only at h; split at h
    · exact varStepR_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      intro e; simp only [rsb] at e; rw [fixT a hra] at e; cases e
  | .var a, .con as t, h, _, _, _ =>
    dsimp only at h; split at h
    · exact varStepR_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      intro e; simp only [rsb] at e; rw [fixT a hra] at e; cases e
  | .record ρ tl, .var b, h, _, _, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepR_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      intro e; simp only [rsb] at e; rw [fixT b hrb] at e; cases e
  | .fn x y, .var b, h, _, _, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepR_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      intro e; simp only [rsb] at e; rw [fixT b hrb] at e; cases e
  | .con as t, .var b, h, _, _, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepR_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      intro e; simp only [rsb] at e; rw [fixT b hrb] at e; cases e
  | .fn _ _, .fn _ _, h, _, _, _ => cases h
  | .con as t, .con bs t', h, _, _, _ =>
    dsimp only at h
    split at h
    · cases h
    · rename_i hc
      simp only [rsb, Ty.con.injEq]
      rintro ⟨h1, h2⟩
      apply hc
      refine ⟨h2, ?_⟩
      have := congrArg List.length h1
      simpa [rsbList_length] using this
  | .record ρ1 t1, .record ρ2 t2, h, _, g, hu =>
    intro _
    exact recStep_fail g h s hs hu
  | .record _ _, .fn _ _, _, _, _, _ => simp [rsb]
  | .record _ _, .con _ _, _, _, _, _ => simp [rsb]
  | .fn _ _, .record _ _, _, _, _, _ => simp [rsb]
  | .fn _ _, .con _ _, _, _, _, _ => simp [rsb]
  | .con _ _, .record _ _, _, _, _, _ => simp [rsb]
  | .con _ _, .fn _ _, _, _, _, _ => simp [rsb]

/-! ## The loop -/

theorem rLoop_ok {R : RRigid} : ∀ (fuel : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) (θ' : RBnd) (n' : Nat),
    NewFlexR R n → GoodR R n θ E X → rLoop R fuel E X θ n = .ok θ' n' →
    ∃ X', GoodR R n' θ' [] X' ∧ n ≤ n' ∧ CorrR R n E X θ [] X' θ'
  | 0, _, _, _, _, _, _, _, _, h => by cases h
  | f + 1, [], X, θ, n, θ', n', _, g, h => by
    simp only [rLoop, ROut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨X, g, Nat.le_refl _, corrR_refl R n [] X θ⟩
  | f + 1, (l, r) :: rest, X, θ, n, θ', n', hN, g, h => by
    simp only [rLoop] at h
    split at h
    · rename_i E1 X1 θ1 n1 hs
      obtain ⟨g1, hn1, c1⟩ := uStepR_next g hs
      obtain ⟨X2, g2, hn2, c2⟩ := rLoop_ok f E1 X1 θ1 n1 θ' n' (hN.mono hn1) g1 h
      exact ⟨X2, g2, Nat.le_trans hn1 hn2, corrR_trans hN hn1 c1 c2⟩
    · cases h

theorem rLoop_fail {R : RRigid} : ∀ (fuel : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat),
    NewFlexR R n → GoodR R n θ E X → rLoop R fuel E X θ n = .fail →
    ∀ s, FixR R s → RespR s → UniR s E X → AbsR s θ → False
  | 0, _, _, _, _, _, _, h => by cases h
  | f + 1, [], _, θ, n, _, _, h => by cases h
  | f + 1, (l, r) :: rest, X, θ, n, hN, g, h => by
    simp only [rLoop] at h
    split at h
    · rename_i E1 X1 θ1 n1 hs
      obtain ⟨g1, hn1, c1⟩ := uStepR_next g hs
      intro s hs' hr hu ha
      obtain ⟨s1, ag, r1, u1, b1⟩ := c1.2 s hs' hr hu ha
      exact rLoop_fail f E1 X1 θ1 n1 (hN.mono hn1) g1 h s1 (fixR_of_agree hN hs' ag) r1 u1 b1
    · rename_i hs
      intro s hs' hr hu _
      exact uStepR_fail g hs s hs' hr hu

/-! ## The mgu theorem (section 4, parts 1 and 2) -/

/-- The initial problem: canonical types, every variable old (below `n`). -/
def ProbOK (n : Nat) (E : Eqs) (X : List Ty) : Prop :=
  (∀ τ ∈ tys E X, cnB τ = true) ∧ ∀ τ ∈ tys E X, ∀ w ∈ τ.vars, newB n w = false

theorem goodR_nil (R : RRigid) {n : Nat} {E : Eqs} {X : List Ty} (hP : ProbOK n E X) : GoodR R n [] E X := by
  have hi : ∀ v, (toRS []).img v = vty v := fun v => by
    rw [img_toRS (fun _ h => absurd h List.not_mem_nil)]; rfl
  refine ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, ?_, ?_, hP.2, fun _ h => absurd h List.not_mem_nil, hP.1⟩
  · intro v w hw
    rw [hi v, vars_vty, List.mem_singleton] at hw; subst hw; exact hi w
  · intro τ _ w _; exact hi w

theorem absR_nil (s : RSub) : AbsR s [] := fun v => by
  rw [img_toRS (fun _ h => absurd h List.not_mem_nil)]; simp only [FMap.find?_nil, Option.getD_none]; rw [rsb_vty]

mutual
/-- A canonical image comes from a canonical type. -/
theorem cnB_of_rsb {s : RSub} : ∀ {τ : Ty}, cnB (rsb s τ) = true → cnB τ = true
  | .var _, _ => rfl
  | .record ρ tl, h => by
    obtain ⟨h1, h2, _⟩ := cnB_rsb_record.mp h
    exact cnB_record.mpr ⟨(sorted_rsbRow_iff s).mp (sorted_of_mrg h1).1, cnRow_of_rsb h2⟩
  | .fn a b, h => by
    simp only [rsb, cnB, Bool.and_eq_true] at h ⊢; exact ⟨cnB_of_rsb h.1, cnB_of_rsb h.2⟩
  | .con as _, h => by simp only [rsb, cnB] at h ⊢; exact cnList_of_rsb h
theorem cnRow_of_rsb {s : RSub} : ∀ {ρ : Row}, (∀ p ∈ ρ, cnB (rsb s p.2) = true) → ∀ p ∈ ρ, cnB p.2 = true
  | [], _, _, hp => nomatch hp
  | (l, x) :: r, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact cnB_of_rsb (h _ (List.mem_cons_self ..))
    · exact cnRow_of_rsb (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp
theorem cnList_of_rsb {s : RSub} : ∀ {ts : List Ty}, cnListB (rsbList s ts) = true → cnListB ts = true
  | [], _ => rfl
  | x :: r, h => by
    simp only [rsbList, cnListB, Bool.and_eq_true] at h ⊢; exact ⟨cnB_of_rsb h.1, cnList_of_rsb h.2⟩
end

theorem mguR_ok {fuel : Nat} {R : RRigid} {n : Nat} {E : Eqs} {X : List Ty} {θ : RBnd} {n' : Nat}
    (hN : NewFlexR R n) (hP : ProbOK n E X) (h : mguR fuel R n E X = .ok θ n') :
    UniR (toRS θ) E X ∧ FixR R (toRS θ) ∧ RespR (toRS θ) ∧ AbsR (toRS θ) θ ∧ n ≤ n' ∧
    ∀ s, FixR R s → RespR s → UniR s E X →
      ∃ T, FixR R T ∧ RespR T ∧ (∀ v, newB n v = false → T.img v = s.img v) ∧ AbsR T θ ∧
        ∀ v, newB n v = false → s.img v = rsb T ((toRS θ).img v) := by
  obtain ⟨X', g, hn, c⟩ := rLoop_ok fuel E X [] n θ n' hN (goodR_nil R hP) h
  have habs : AbsR (toRS θ) θ := fun v => rsb_eq_self fun w hw => g.idem v w hw
  have hfix : FixR R (toRS θ) := by
    intro v hv
    rw [img_toRS g.rrec]
    cases hf : FMap.find? θ v with
    | none => rfl
    | some τ => have := g.keys _ (rfind?_mem hf); simp only at this; rw [hv] at this; cases this
  have hresp : RespR (toRS θ) := by
    intro a
    have := img_toRS g.rrec (.ty a)
    simp only [RSub.img] at this; rw [this]
    cases hf : FMap.find? θ (.ty a) with
    | none => exact admC_self a
    | some τ => exact g.adm _ (rfind?_mem hf) a rfl
  have hu0 : UniR (toRS θ) [] X' := by
    refine ⟨fun _ h => absurd h List.not_mem_nil, fun τ hτ => ?_⟩
    rw [rsb_eq_self fun w hw => g.stable τ hτ w hw]; exact g.cn τ hτ
  refine ⟨(c.1 _ hu0 habs).1, hfix, hresp, habs, hn, ?_⟩
  intro s hs hr hu
  obtain ⟨T, ag, rT, _, aT⟩ := c.2 s hs hr hu (absR_nil s)
  exact ⟨T, fixR_of_agree hN hs ag, rT, ag, aT, fun v hv => by rw [aT v, ag v hv]⟩

theorem mguR_fail {fuel : Nat} {R : RRigid} {n : Nat} {E : Eqs} {X : List Ty}
    (hN : NewFlexR R n) (hold : ∀ τ ∈ tys E X, ∀ w ∈ τ.vars, newB n w = false) (h : mguR fuel R n E X = .fail) :
    ∀ s, FixR R s → RespR s → ¬ UniR s E X := fun s hs hr hu =>
  rLoop_fail fuel E X [] n hN (goodR_nil R ⟨fun τ hτ => cnB_of_rsb (hu.2 τ hτ), hold⟩) h s hs hr hu (absR_nil s)

end StandardElm.Stat.Complete
