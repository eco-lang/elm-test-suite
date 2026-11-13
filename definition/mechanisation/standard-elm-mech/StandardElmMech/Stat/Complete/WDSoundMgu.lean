/-
  A Standard Definition of Elm? Mechanisation: the structure of a run of the unification with
  rows (`rLoop`, MguR.lean), for L10 of plan step 11, milestone (d).

  MguRLoop.lean's `rLoop_ok` needs the problem canonical (`GoodR`'s `cn`); W's soundness (L10)
  cannot assume it: a type with a repeated label under the current substitution can reach a
  unification of a run whose result is refused later. What the soundness needs of every
  successful unification is structural, and holds without canonicity (`rLoop_struct`):

  * the substitution stays good (`GoodR _ _ _ [] []`: flexible keys, admissible type bindings,
    rows to records, idempotent, old);
  * the new substitution absorbs the old one;
  * it moves only variables of the equations and new ones (`MovesD`, as MguCVars.lean's
    `cLoop_inv` for W): every variable it binds that the old one did not, and every variable of
    such a binding's image, is a variable of the equations or new.

  A step either keeps the substitution (the variables of the new equations among those of the
  old and the new variables) or binds a variable of the equations, unbound, to a type of
  variables of the equations and new ones (twice for a record step with two tails).
-/
import StandardElmMech.Stat.Complete.WDTheorems
import StandardElmMech.Stat.Complete.MguCVars

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

namespace WDS

/-! ## Substitutions: absorption, idempotence, moves -/

/-- `t ∘ s = t`. -/
def AbsS (t s : RSub) : Prop := ∀ v, rsb t (s.img v) = t.img v

def IdemS (s : RSub) : Prop := ∀ v, ∀ w ∈ (s.img v).vars, s.img w = vty w

/-- Every variable `θ'` binds that `θ` did not, and every variable of its image, has `P`. -/
def MovesD (P : BVar → Prop) (θ θ' : RSub) : Prop :=
  ∀ d, θ.img d = vty d → θ'.img d ≠ vty d → P d ∧ ∀ w ∈ (θ'.img d).vars, P w

theorem absS_comp {t s : RSub} (h : AbsS t s) : rcomp t s = t :=
  RSub.eq_of_img fun v => by rw [img_rcomp]; exact h v

theorem absS_rsb {t s : RSub} (h : AbsS t s) (τ : Ty) : rsb t (rsb s τ) = rsb t τ := by
  rw [rsb_rsb, absS_comp h]

theorem absS_trans {u t s : RSub} (h2 : AbsS u t) (h1 : AbsS t s) : AbsS u s := fun v => by
  rw [← h2 v, ← h1 v, absS_rsb h2]

theorem absS_self {s : RSub} (h : IdemS s) : AbsS s s := fun v => rsb_eq_self fun w hw => h v w hw

theorem idemS_of_good {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X) :
    IdemS (toRS θ) := g.idem

theorem moves_refl (P : BVar → Prop) (θ : RSub) : MovesD P θ θ := fun _ h1 h2 => absurd h1 h2

theorem moves_mono {P Q : BVar → Prop} {θ θ' : RSub} (h : MovesD P θ θ') (hPQ : ∀ b, P b → Q b) :
    MovesD Q θ θ' := fun d h1 h2 => ⟨hPQ _ (h d h1 h2).1, fun b hb => hPQ _ ((h d h1 h2).2 b hb)⟩

/-- A variable of an image under the later substitution: of the image under the earlier one and
    fixed, or of a moved variable's image. -/
theorem moves_ty {P : BVar → Prop} {θ θ' : RSub} (hm : MovesD P θ θ') (ha : AbsS θ' θ) (hi : IdemS θ)
    (τ : Ty) (b : BVar) (hb : b ∈ (rsb θ' τ).vars) :
    (b ∈ (rsb θ τ).vars ∧ θ'.img b = vty b) ∨
      ∃ e, e ∈ (rsb θ τ).vars ∧ θ.img e = vty e ∧ θ'.img e ≠ vty e ∧ P e ∧ P b ∧ b ∈ (θ'.img e).vars := by
  rw [← absS_rsb ha] at hb
  obtain ⟨e, he, hbe⟩ := (mem_vars_rsb _ _ b).mp hb
  have hθe : θ.img e = vty e := by
    obtain ⟨c, _, hc⟩ := (mem_vars_rsb _ _ e).mp he; exact hi c e hc
  by_cases h : θ'.img e = vty e
  · rw [h, vars_vty, List.mem_singleton] at hbe; subst hbe
    exact .inl ⟨he, h⟩
  · exact .inr ⟨e, he, hθe, h, (hm e hθe h).1, (hm e hθe h).2 b hbe, hbe⟩

theorem moves_ty' {P : BVar → Prop} {θ θ' : RSub} (hm : MovesD P θ θ') (ha : AbsS θ' θ) (hi : IdemS θ)
    (τ : Ty) (b : BVar) (hb : b ∈ (rsb θ' τ).vars) : b ∈ (rsb θ τ).vars ∨ P b := by
  rcases moves_ty hm ha hi τ b hb with h | ⟨_, _, _, _, _, h, _⟩
  · exact .inl h.1
  · exact .inr h

theorem moves_var {P : BVar → Prop} {θ θ' : RSub} (hm : MovesD P θ θ') (ha : AbsS θ' θ) (hi : IdemS θ)
    (x b : BVar) (hb : b ∈ (θ'.img x).vars) : b ∈ (θ.img x).vars ∨ P b := by
  have := moves_ty' hm ha hi (vty x) b (by rw [rsb_vty]; exact hb)
  rwa [rsb_vty] at this

theorem moves_trans {P : BVar → Prop} {θ θ1 θ2 : RSub} (h1 : MovesD P θ θ1) (h2 : MovesD P θ1 θ2)
    (ha : AbsS θ2 θ1) (hi : IdemS θ1) : MovesD P θ θ2 := by
  intro d hd hd2
  by_cases hd1 : θ1.img d = vty d
  · exact h2 d hd1 hd2
  · refine ⟨(h1 d hd hd1).1, fun b hb => ?_⟩
    rcases moves_var h2 ha hi d b hb with h | h
    · exact (h1 d hd hd1).2 b h
    · exact h

/-! ## One binding -/

theorem img_bindR {v : BVar} {τ : Ty} {θ : RBnd} (hθ : RowRec θ) (hτ : IsRec v τ) (w : BVar) :
    (toRS (bindR v τ θ)).img w = if v = w then τ else rsb (one v τ) ((toRS θ).img w) := by
  rw [img_toRS (rowRec_bindR hθ hτ), find?_bindR]
  split
  · rfl
  · rename_i hw
    rw [img_toRS hθ]
    cases hf : FMap.find? θ w with
    | none => simp only [Option.map_none, Option.getD_none]; rw [rsb_vty, img_one_ne τ (fun e => hw e.symm)]
    | some σ => rfl

theorem vars_rsb_one {v w : BVar} {τ σ : Ty} (hv : IsRec v τ) (h : w ∈ (rsb (one v τ) σ).vars) :
    (w ∈ σ.vars ∧ w ≠ v) ∨ w ∈ τ.vars := by
  obtain ⟨u, hu, hwu⟩ := (mem_vars_rsb _ _ w).mp h
  by_cases e : u = v
  · subst e; rw [img_one_self hv] at hwu; exact .inr hwu
  · rw [img_one_ne τ e, vars_vty, List.mem_singleton] at hwu; subst hwu; exact .inl ⟨hu, e⟩

theorem respR_one {v : BVar} {τ : Ty} (hadm : ∀ a, v = .ty a → Adm a.cls τ) : RespR (one v τ) := fun a => by
  show Adm a.cls ((FMap.find? [(v, τ)] (.ty a)).getD (.var a))
  simp only [FMap.find?]
  split
  · rename_i h; exact hadm a h
  · exact admC_self a

theorem unbound_of_new {R : RRigid} {n : Nat} {θ : RBnd} (g : GoodR R n θ [] []) {v : BVar}
    (h : newB n v = true) : (toRS θ).img v = vty v := by
  rcases img_old g v with e | ⟨e, -⟩
  · exact e
  · rw [h] at e; cases e

/-- The equations' variables: unbound, old. -/
def EOk (θ : RBnd) (n : Nat) (E : Eqs) : Prop := ∀ w ∈ bvars E, (toRS θ).img w = vty w ∧ newB n w = false

theorem EOk.mono {θ : RBnd} {n m : Nat} {E : Eqs} (h : EOk θ n E) (hm : n ≤ m) : EOk θ m E :=
  fun w hw => ⟨(h w hw).1, newB_mono hm (h w hw).2⟩

theorem EOk.sub {θ : RBnd} {n : Nat} {E E' : Eqs} (h : EOk θ n E) (hs : ∀ w ∈ bvars E', w ∈ bvars E) : EOk θ n E' :=
  fun w hw => h w (hs w hw)

theorem bvars_sE {v w : BVar} {τ : Ty} {E : Eqs} (hv : IsRec v τ) (h : w ∈ bvars (sE (one v τ) E)) :
    (w ∈ bvars E ∧ w ≠ v) ∨ w ∈ τ.vars := by
  obtain ⟨e, he, hw⟩ := mem_bvars.mp h
  simp only [sE, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rcases hw with hw | hw
  · rcases vars_rsb_one hv hw with ⟨h1, h2⟩ | h1
    · exact .inl ⟨mem_bvars.mpr ⟨e0, he0, .inl h1⟩, h2⟩
    · exact .inr h1
  · rcases vars_rsb_one hv hw with ⟨h1, h2⟩ | h1
    · exact .inl ⟨mem_bvars.mpr ⟨e0, he0, .inr h1⟩, h2⟩
    · exact .inr h1

section bind
variable {R : RRigid} {n n' : Nat} {θ : RBnd} {v : BVar} {τ : Ty}

/-- After binding `v ↦ τ`: a variable unbound before and other than `v` is unbound, and so is a
    variable of `τ`. -/
theorem unbound_bind (hθ : RowRec θ) (hrec : IsRec v τ) (hocc : v ∉ τ.vars)
    (hτ : ∀ w ∈ τ.vars, (toRS θ).img w = vty w) {w : BVar}
    (hw : ((toRS θ).img w = vty w ∧ w ≠ v) ∨ w ∈ τ.vars) : (toRS (bindR v τ θ)).img w = vty w := by
  have hw' : (toRS θ).img w = vty w ∧ w ≠ v := by
    rcases hw with h | h
    · exact h
    · exact ⟨hτ w h, fun e => hocc (e ▸ h)⟩
  rw [img_bindR hθ hrec, if_neg (fun e => hw'.2 e.symm), hw'.1, rsb_vty, img_one_ne τ hw'.2]

theorem goodR_bind (g : GoodR R n θ [] []) (hv : (toRS θ).img v = vty v) (hvo : newB n' v = false)
    (hR : R v = false) (hocc : v ∉ τ.vars) (hrec : IsRec v τ) (hadm : ∀ a, v = .ty a → Adm a.cls τ)
    (hτ : ∀ w ∈ τ.vars, (toRS θ).img w = vty w ∧ newB n' w = false) (hn : n ≤ n') :
    GoodR R n' (bindR v τ θ) [] [] := by
  have hrr := rowRec_bindR g.rrec hrec
  refine ⟨fun p hp => ?_, fun p hp a ha => ?_, hrr, fun d w hw => ?_, fun _ h => by simp [tys] at h,
    fun _ h => by simp [tys] at h, fun p hp => ?_, fun _ h => by simp [tys] at h⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact hR
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact g.keys q hq
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact hadm a ha
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact admR_rsb (respR_one hadm) (g.adm q hq a ha)
  · rw [img_bindR g.rrec hrec] at hw
    refine unbound_bind g.rrec hrec hocc (fun w hw => (hτ w hw).1) ?_
    split at hw
    · exact .inr hw
    · rcases vars_rsb_one hrec hw with ⟨h1, h2⟩ | h1
      · exact .inl ⟨g.idem d w h1, h2⟩
      · exact .inr h1
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hvo, fun w hw => (hτ w hw).2⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      refine ⟨newB_mono hn (g.oldθ q hq).1, fun w hw => ?_⟩
      rcases vars_rsb_one hrec hw with ⟨h1, -⟩ | h1
      · exact newB_mono hn ((g.oldθ q hq).2 w h1)
      · exact (hτ w h1).2

theorem absS_bind (g : GoodR R n θ [] []) (hv : (toRS θ).img v = vty v) (hrec : IsRec v τ) :
    AbsS (toRS (bindR v τ θ)) (toRS θ) := fun w => by
  rw [toRS_bindR g.rrec hrec hv, ← rsb_rsb, rsb_eq_self (s := toRS θ) fun u hu => g.idem w u hu, img_rcomp]

theorem moves_bind (g : GoodR R n θ [] []) (hrec : IsRec v τ) :
    MovesD (fun w => w = v ∨ w ∈ τ.vars) (toRS θ) (toRS (bindR v τ θ)) := by
  intro d hd hd'
  rw [img_bindR g.rrec hrec] at hd' ⊢
  split at hd'
  · rename_i e; subst e
    rw [if_pos rfl]; exact ⟨.inl rfl, fun w hw => .inr hw⟩
  · rename_i e
    rw [hd, rsb_vty, img_one_ne τ (fun h => e h.symm)] at hd'; exact absurd rfl hd'

end bind

/-! ## A step -/

/-- What a step of a successful run keeps, for the variables `Q` of its equations and the new
    ones. -/
structure StepOK (R : RRigid) (n : Nat) (θ : RBnd) (Q : BVar → Prop) (n' : Nat) (θ' : RBnd) (E' : Eqs) : Prop where
  good : GoodR R n' θ' [] []
  eok : EOk θ' n' E'
  le : n ≤ n'
  abs : AbsS (toRS θ') (toRS θ)
  mv : MovesD Q (toRS θ) (toRS θ')
  sub : ∀ w ∈ bvars E', Q w

theorem StepOK.same {R : RRigid} {n : Nat} {θ : RBnd} {Q : BVar → Prop} {E' : Eqs} (g : GoodR R n θ [] [])
    (he : EOk θ n E') (hs : ∀ w ∈ bvars E', Q w) : StepOK R n θ Q n θ E' :=
  ⟨g, he, Nat.le_refl _, absS_self g.idem, moves_refl _ _, hs⟩

theorem StepOK.bind {R : RRigid} {n n' : Nat} {θ : RBnd} {Q : BVar → Prop} {v : BVar} {τ : Ty} {E : Eqs}
    (g : GoodR R n θ [] []) (hv : (toRS θ).img v = vty v) (hvo : newB n' v = false)
    (hR : R v = false) (hocc : v ∉ τ.vars) (hrec : IsRec v τ) (hadm : ∀ a, v = .ty a → Adm a.cls τ)
    (hτ : ∀ w ∈ τ.vars, (toRS θ).img w = vty w ∧ newB n' w = false) (hn : n ≤ n') (hE : EOk θ n' E)
    (hQv : Q v) (hQτ : ∀ w ∈ τ.vars, Q w) (hQE : ∀ w ∈ bvars E, Q w) :
    StepOK R n θ Q n' (bindR v τ θ) (sE (one v τ) E) := by
  refine ⟨goodR_bind g hv hvo hR hocc hrec hadm hτ hn, fun w hw => ?_, hn, absS_bind g hv hrec,
    moves_mono (moves_bind g hrec) (fun w hw => hw.elim (fun e => e ▸ hQv) (hQτ w)), fun w hw => ?_⟩
  · refine ⟨unbound_bind g.rrec hrec hocc (fun w hw => (hτ w hw).1) ?_, ?_⟩
    · rcases bvars_sE hrec hw with ⟨h1, h2⟩ | h1
      · exact .inl ⟨(hE w h1).1, h2⟩
      · exact .inr h1
    · rcases bvars_sE hrec hw with ⟨h1, -⟩ | h1
      · exact (hE w h1).2
      · exact (hτ w h1).2
  · rcases bvars_sE hrec hw with ⟨h1, -⟩ | h1
    · exact hQE w h1
    · exact hQτ w h1

theorem StepOK.trans {R : RRigid} {n n1 n2 : Nat} {θ θ1 θ2 : RBnd} {Q : BVar → Prop} {E1 E2 : Eqs}
    (h1 : StepOK R n θ Q n1 θ1 E1) (h2 : StepOK R n1 θ1 Q n2 θ2 E2) (hθ : IdemS (toRS θ)) : StepOK R n θ Q n2 θ2 E2 :=
  ⟨h2.good, h2.eok, Nat.le_trans h1.le h2.le, absS_trans h2.abs h1.abs,
    moves_trans h1.mv h2.mv h2.abs h1.good.idem, h2.sub⟩

/-- The variables of a step's equations and the new ones. -/
def InE (E : Eqs) (n : Nat) (w : BVar) : Prop := w ∈ bvars E ∨ newB n w = true

section step
variable {R : RRigid} {n : Nat} {θ : RBnd}

theorem fresh_new (n : Nat) (m : Cls) : newB n (.ty (.fresh n m)) = true := by simp [newB, TyVar.isNew]

theorem fresh_old (n : Nat) (m : Cls) : newB (n + 1) (.ty (.fresh n m)) = false := by simp [newB, TyVar.isNew]

theorem ne_of_old_new {n : Nat} {v w : BVar} (h1 : newB n v = false) (h2 : newB n w = true) : v ≠ w := by
  rintro rfl; rw [h1] at h2; cases h2

/-- A refinement of the type variable `b` of the equations to a fresh variable. -/
theorem refine_step {E : Eqs} {X : List Ty} {b : TyVar} {m : Cls} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ [] []) (hE : EOk θ n E) (hb : BVar.ty b ∈ bvars E) (hR : R (.ty b) = false)
    (hm : m.le b.cls = true) (h : refineS b m E X θ n = .next E' X' θ' n') : StepOK R n θ (InE E n) n' θ' E' := by
  simp only [refineS, bindS, RStep.next.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  have hfn := fresh_new n m
  have hvars : ∀ w ∈ (Ty.var (.fresh n m)).vars, w = .ty (.fresh n m) := fun w hw => by
    simpa [Ty.vars] using hw
  refine StepOK.bind g (hE _ hb).1 (newB_mono (Nat.le_succ n) (hE _ hb).2) hR ?_ trivial
    (fun a e => by cases e; exact admC_var_iff.mpr hm) (fun w hw => ?_) (Nat.le_succ n) (hE.mono (Nat.le_succ n))
    (.inl hb) (fun w hw => .inr (by rw [hvars w hw]; exact hfn)) (fun w hw => .inl hw)
  · intro hm'; rw [hvars _ hm'] at hb; exact ne_of_old_new (hE _ hb).2 hfn rfl
  · rw [hvars w hw]; exact ⟨unbound_of_new g hfn, fresh_old n m⟩

/-- A binding of the type variable `a` of the equations to a type of variables of the
    equations. -/
theorem tybind_step {E rest : Eqs} {a : TyVar} {τ : Ty} (g : GoodR R n θ [] []) (hE : EOk θ n E)
    (ha : BVar.ty a ∈ bvars E) (hτ : ∀ w ∈ τ.vars, w ∈ bvars E) (hrest : ∀ w ∈ bvars rest, w ∈ bvars E)
    (hR : R (.ty a) = false) (hocc : BVar.ty a ∉ τ.vars) (hadm : Adm a.cls τ) :
    StepOK R n θ (InE E n) n (bindR (.ty a) τ θ) (sE (one (.ty a) τ) rest) :=
  StepOK.bind g (hE _ ha).1 (hE _ ha).2 hR hocc trivial (fun b e => by cases e; exact hadm)
    (fun w hw => hE w (hτ w hw)) (Nat.le_refl _) (hE.sub hrest) (.inl ha) (fun w hw => .inl (hτ w hw))
    (fun w hw => .inl (hrest w hw))

theorem varStepR_struct {a : TyVar} {τ : Ty} {cur rest : Eqs} {X : List Ty} {E' : Eqs} {X' : List Ty} {θ' : RBnd}
    {n' : Nat} (g : GoodR R n θ [] []) (hE : EOk θ n cur) (ha : BVar.ty a ∈ bvars cur) (hτ : ∀ w ∈ τ.vars, w ∈ bvars cur)
    (hrest : ∀ w ∈ bvars rest, w ∈ bvars cur) (hR : R (.ty a) = false)
    (h : varStepR R a τ cur rest X θ n = .next E' X' θ' n') : StepOK R n θ (InE cur n) n' θ' E' := by
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
        exact tybind_step g hE ha hτ hrest hR hocc (adm_of_req hps (refineTarget_all (by assumption)))
      · rename_i b m ht
        obtain ⟨k, hk, hRb, hm, hle⟩ := refineTarget_some ht
        have hbτ : BVar.ty b ∈ τ.vars := reqC_vars _ _ _ hps _ hk
        exact refine_step g hE (hτ _ hbτ) hRb (meet_lt hm hle).1 h

end step

/-! ## The record step -/

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {rest : Eqs} {X : List Ty}

theorem bvars_common {w : BVar} (h : w ∈ bvars (commonEqs ρ1 ρ2 ++ rest)) :
    w ∈ (Ty.record ρ1 none).vars ∨ w ∈ (Ty.record ρ2 none).vars ∨ w ∈ bvars rest := by
  obtain ⟨e, he, hw⟩ := mem_bvars.mp h
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l, h1, h2⟩ := commonEqs_fields he
    rcases hw with hw | hw
    · exact .inl (field_vars h1 hw)
    · exact .inr (.inl (field_vars h2 hw))
  · exact .inr (.inr (mem_bvars.mpr ⟨e, he, hw⟩))

theorem rec_vars_l {t1 t2 : Option RowVar} {w : BVar} (h : w ∈ (Ty.record ρ1 none).vars) :
    w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  refine bvars_cons.mpr (.inl ?_)
  rw [vars_record] at h ⊢; simp only [tailVars, List.append_nil] at h; exact List.mem_append_left _ h

theorem rec_vars_r {t1 t2 : Option RowVar} {w : BVar} (h : w ∈ (Ty.record ρ2 none).vars) :
    w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  refine bvars_cons.mpr (.inr (.inl ?_))
  rw [vars_record] at h ⊢; simp only [tailVars, List.append_nil] at h; exact List.mem_append_left _ h

theorem rec_tail_l {t2 : Option RowVar} {e : RowVar} :
    BVar.row e ∈ bvars ((.record ρ1 (some e), .record ρ2 t2) :: rest) := bvars_cons.mpr (.inl tail_vars)

theorem rec_tail_r {t1 : Option RowVar} {e : RowVar} :
    BVar.row e ∈ bvars ((.record ρ1 t1, .record ρ2 (some e)) :: rest) := bvars_cons.mpr (.inr (.inl tail_vars))

theorem only_vars {w : BVar} {ρa ρb : Row} (h : w ∈ Ty.rowVars (onlyL ρa ρb)) : w ∈ (Ty.record ρa none).vars := by
  obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp h
  exact field_vars (mem_onlyL.mp hp).1 hw

/-- A row binding of the step. -/
theorem rowbind_step {t1 t2 : Option RowVar} {e : RowVar} {ϱ : Row} {t : Option RowVar} {X1 : List Ty}
    {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ [] []) (hE : EOk θ n ((.record ρ1 t1, .record ρ2 t2) :: rest))
    (he : BVar.row e ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest))
    (hϱ : ∀ w ∈ (Ty.record ϱ t).vars, w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest))
    (h : bindRow R e ϱ t (commonEqs ρ1 ρ2 ++ rest) X1 θ n = .next E' X' θ' n') :
    StepOK R n θ (InE ((.record ρ1 t1, .record ρ2 t2) :: rest) n) n' θ' E' := by
  obtain ⟨hR, hocc, -, rfl, -, rfl, rfl⟩ := bindRow_next h
  have hsub : ∀ w ∈ bvars (commonEqs ρ1 ρ2 ++ rest), w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
    intro w hw
    rcases bvars_common hw with h' | h' | h'
    · exact rec_vars_l h'
    · exact rec_vars_r h'
    · exact bvars_cons.mpr (.inr (.inr h'))
  exact StepOK.bind g (hE _ he).1 (hE _ he).2 hR hocc ⟨_, _, rfl⟩ (fun a e' => by cases e')
    (fun w hw => hE w (hϱ w hw)) (Nat.le_refl _) (hE.sub hsub) (.inl he) (fun w hw => .inl (hϱ w hw))
    (fun w hw => .inl (hsub w hw))

theorem recStep_struct {t1 t2 : Option RowVar} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ [] []) (hE : EOk θ n ((.record ρ1 t1, .record ρ2 t2) :: rest))
    (h : recStep R ρ1 t1 ρ2 t2 rest (.record ρ1 t1 :: X) θ n = .next E' X' θ' n') :
    StepOK R n θ (InE ((.record ρ1 t1, .record ρ2 t2) :: rest) n) n' θ' E' := by
  have hsub : ∀ w ∈ bvars (commonEqs ρ1 ρ2 ++ rest), w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
    intro w hw
    rcases bvars_common hw with h' | h' | h'
    · exact rec_vars_l h'
    · exact rec_vars_r h'
    · exact bvars_cons.mpr (.inr (.inr h'))
  have same : StepOK R n θ (InE ((.record ρ1 t1, .record ρ2 t2) :: rest) n) n θ (commonEqs ρ1 ρ2 ++ rest) :=
    StepOK.same g (hE.sub hsub) fun w hw => .inl (hsub w hw)
  -- the type a tail is bound to: fields of a side and a tail of the equation (or none)
  have tyok : ∀ (o : Row) (t : Option RowVar), (∀ w ∈ Ty.rowVars o, w ∈ (Ty.record ρ1 none).vars ∨
      w ∈ (Ty.record ρ2 none).vars) → (∀ e, t = some e → BVar.row e ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest)) →
      ∀ w ∈ (Ty.record o t).vars, w ∈ bvars ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
    intro o t ho ht w hw
    rw [vars_record] at hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases ho w hw with h' | h'
      · exact rec_vars_l h'
      · exact rec_vars_r h'
    · cases t with
      | none => cases hw
      | some e =>
        simp only [tailVars, List.mem_singleton] at hw; subst hw; exact ht e rfl
  cases t1 with
  | none =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · cases h; exact same
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · exact rowbind_step g hE rec_tail_r
          (tyok _ none (fun w hw => .inl (only_vars hw)) (fun _ h => by cases h)) h
      · cases h
  | some e1 =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · exact rowbind_step g hE rec_tail_l
          (tyok _ none (fun w hw => .inr (only_vars hw)) (fun _ h => by cases h)) h
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · split at h
        · cases h; exact same
        · cases h
      · rename_i hne
        split at h
        · split at h
          · split at h
            · exact rowbind_step g hE rec_tail_l
                (tyok [] _ (fun w hw => by cases hw) (fun e he => by cases he; exact rec_tail_r)) h
            · exact rowbind_step g hE rec_tail_r
                (tyok [] _ (fun w hw => by cases hw) (fun e he => by cases he; exact rec_tail_l)) h
          · exact rowbind_step g hE rec_tail_r
              (tyok _ _ (fun w hw => .inl (only_vars hw)) (fun e he => by cases he; exact rec_tail_l)) h
        · split at h
          · exact rowbind_step g hE rec_tail_l
              (tyok _ _ (fun w hw => .inr (only_vars hw)) (fun e he => by cases he; exact rec_tail_r)) h
          · split at h
            · rename_i F1 X1 θ1 n1 hb1
              -- the first binding `e1 ↦ ⟨o2 | ε⟩`, `ε` fresh
              obtain ⟨hR1, hocc1, -, rfl, -, rfl, rfl⟩ := bindRow_next hb1
              have hεn : newB n (.row (.fresh n)) = true := newB_fresh_self n
              have hεo : newB (n + 1) (.row (.fresh n)) = false := newB_fresh_succ n
              have hτ1 : ∀ w ∈ (Ty.record (onlyL ρ2 ρ1) (some (.fresh n))).vars,
                  InE ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) n w ∧
                  (toRS θ).img w = vty w ∧ newB (n + 1) w = false := by
                intro w hw
                rw [vars_record] at hw
                rcases List.mem_append.mp hw with hw | hw
                · have := rec_vars_r (ρ1 := ρ1) (t1 := some e1) (t2 := some e2) (rest := rest) (only_vars hw)
                  exact ⟨.inl this, (hE w this).1, newB_mono (Nat.le_succ n) (hE w this).2⟩
                · simp only [tailVars, List.mem_singleton] at hw; subst hw
                  exact ⟨.inr hεn, unbound_of_new g hεn, hεo⟩
              have S1 : StepOK R n θ (InE ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) n) (n + 1)
                  (bindR (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) θ)
                  (sE (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (commonEqs ρ1 ρ2 ++ rest)) :=
                StepOK.bind g (hE _ rec_tail_l).1 (newB_mono (Nat.le_succ n) (hE _ rec_tail_l).2) hR1 hocc1
                  ⟨_, _, rfl⟩ (fun a e' => by cases e') (fun w hw => (hτ1 w hw).2) (Nat.le_succ n)
                  ((hE.sub hsub).mono (Nat.le_succ n)) (.inl rec_tail_l) (fun w hw => (hτ1 w hw).1)
                  (fun w hw => .inl (hsub w hw))
              -- the second binding `e2 ↦ ⟨o1' | ε⟩`
              obtain ⟨hR2, hocc2, -, rfl, -, rfl, rfl⟩ := bindRow_next h
              have hrec1 : IsRec (.row e1) (Ty.record (onlyL ρ2 ρ1) (some (.fresh n))) := ⟨_, _, rfl⟩
              have hτ2 : ∀ w ∈ (Ty.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n)))) (onlyL ρ1 ρ2))
                  (some (.fresh n))).vars, InE ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) n w ∧
                  (toRS (bindR (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) θ)).img w = vty w ∧
                  newB (n + 1) w = false := by
                intro w hw
                have hw' : ((toRS θ).img w = vty w ∧ w ≠ .row e1 ∧
                    InE ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) n w ∧ newB (n + 1) w = false) ∨
                    w ∈ (Ty.record (onlyL ρ2 ρ1) (some (.fresh n))).vars := by
                  rw [vars_record] at hw
                  rcases List.mem_append.mp hw with hw | hw
                  · obtain ⟨p, hp, hwp⟩ := mem_rowVarsR.mp hw
                    obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hp
                    rcases vars_rsb_one hrec1 hwp with ⟨h1, h2⟩ | h1
                    · have := rec_vars_l (ρ2 := ρ2) (t1 := some e1) (t2 := some e2) (rest := rest)
                        (field_vars (mem_onlyL.mp hq).1 h1)
                      exact .inl ⟨(hE w this).1, h2, .inl this, newB_mono (Nat.le_succ n) (hE w this).2⟩
                    · exact .inr h1
                  · simp only [tailVars, List.mem_singleton] at hw; subst hw
                    exact .inr (by rw [vars_record]; simp [tailVars])
                rcases hw' with ⟨h1, h2, h3, h4⟩ | h1
                · exact ⟨h3, unbound_bind g.rrec hrec1 hocc1 (fun w hw => (hτ1 w hw).2.1) (.inl ⟨h1, h2⟩), h4⟩
                · exact ⟨(hτ1 w h1).1, unbound_bind g.rrec hrec1 hocc1 (fun w hw => (hτ1 w hw).2.1) (.inr h1),
                    (hτ1 w h1).2.2⟩
              have he2 : (toRS (bindR (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))) θ)).img (.row e2) =
                  vty (.row e2) :=
                unbound_bind g.rrec hrec1 hocc1 (fun w hw => (hτ1 w hw).2.1)
                  (.inl ⟨(hE _ rec_tail_r).1, fun e => hne (by injection e with e; exact e.symm)⟩)
              have S2 := StepOK.bind (Q := InE ((.record ρ1 (some e1), .record ρ2 (some e2)) :: rest) n)
                S1.good he2 (newB_mono (Nat.le_succ n) (hE _ rec_tail_r).2) hR2 hocc2 ⟨_, _, rfl⟩
                (fun a e' => by cases e') (fun w hw => (hτ2 w hw).2) (Nat.le_refl _) S1.eok (.inl rec_tail_r)
                (fun w hw => (hτ2 w hw).1) S1.sub
              exact S1.trans S2 g.idem
            · cases h
end rec

/-! ## A step and the loop -/

theorem uStepR_struct {R : RRigid} {n : Nat} {θ : RBnd} {l r : Ty} {rest : Eqs} {X : List Ty}
    {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (g : GoodR R n θ [] []) (hE : EOk θ n ((l, r) :: rest)) (h : uStepR R θ n l r rest X = .next E' X' θ' n') :
    StepOK R n θ (InE ((l, r) :: rest) n) n' θ' E' := by
  have hl : ∀ w ∈ l.vars, w ∈ bvars ((l, r) :: rest) := fun w hw => bvars_cons.mpr (.inl hw)
  have hr : ∀ w ∈ r.vars, w ∈ bvars ((l, r) :: rest) := fun w hw => bvars_cons.mpr (.inr (.inl hw))
  have hrest : ∀ w ∈ bvars rest, w ∈ bvars ((l, r) :: rest) := fun w hw => bvars_cons.mpr (.inr (.inr hw))
  have same : ∀ {E1 : Eqs}, (∀ w ∈ bvars E1, w ∈ bvars ((l, r) :: rest)) → StepOK R n θ (InE ((l, r) :: rest) n) n θ E1 :=
    fun hs => StepOK.same g (hE.sub hs) fun w hw => .inl (hs w hw)
  unfold uStepR at h
  split at h
  · cases h; exact same hrest
  · split at h
    · -- var, var
      rename_i a b hab
      have hab' : a ≠ b := fun e => hab (by rw [e])
      have nab : BVar.ty a ∉ (Ty.var b).vars := by simpa [Ty.vars] using hab'
      have nba : BVar.ty b ∉ (Ty.var a).vars := by simpa [Ty.vars] using fun e => hab' e.symm
      have ha := hl _ (mem_vars_var a)
      have hb := hr _ (mem_vars_var b)
      have va : ∀ w ∈ (Ty.var a).vars, w ∈ bvars ((Ty.var a, Ty.var b) :: rest) := hl
      have vb : ∀ w ∈ (Ty.var b).vars, w ∈ bvars ((Ty.var a, Ty.var b) :: rest) := hr
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
            exact tybind_step g hE ha vb hrest hfl.1 nab (admC_var_iff.mpr hma)
          · split at h
            · rename_i _ e; subst e
              simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact tybind_step g hE hb va hrest hfl.2 nba (admC_var_iff.mpr hmb)
            · exact refine_step g hE ha hfl.1 hma h
      · split at h
        · rename_i hra
          simp only [Bool.not_eq_true'] at hra
          split at h
          · rename_i hle
            simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact tybind_step g hE ha vb hrest hra nab (admC_var_iff.mpr hle)
          · cases h
        · split at h
          · rename_i _ hrb
            simp only [Bool.not_eq_true'] at hrb
            split at h
            · rename_i hle
              simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact tybind_step g hE hb va hrest hrb nba (admC_var_iff.mpr hle)
            · cases h
          · cases h
    · -- var, non-var
      rename_i a _ _
      split at h
      · rename_i hra
        simp only [Bool.not_eq_true'] at hra
        exact varStepR_struct g hE (hl _ (mem_vars_var a)) hr hrest hra h
      · cases h
    · -- non-var, var
      rename_i b _ _
      split at h
      · rename_i hrb
        simp only [Bool.not_eq_true'] at hrb
        exact varStepR_struct g hE (hr _ (mem_vars_var b)) hl hrest hrb h
      · cases h
    · -- fn, fn
      cases h
      refine same fun w hw => ?_
      simp only [bvars_cons] at hw
      rcases hw with h' | h' | h' | h' | h'
      · exact hl w (by simp [Ty.vars, h'])
      · exact hr w (by simp [Ty.vars, h'])
      · exact hl w (by simp [Ty.vars, h'])
      · exact hr w (by simp [Ty.vars, h'])
      · exact hrest w h'
    · -- con, con
      split at h
      · rename_i as t bs t' _ _
        cases h
        refine same fun w hw => ?_
        obtain ⟨e, he, hwe⟩ := mem_bvars.mp hw
        rcases List.mem_append.mp he with he | he
        · rcases zip_bvars as bs w (mem_bvars.mpr ⟨e, he, hwe⟩) with h' | h'
          · exact hl w (by simpa [Ty.vars] using h')
          · exact hr w (by simpa [Ty.vars] using h')
        · exact hrest w (mem_bvars.mpr ⟨e, he, hwe⟩)
      · cases h
    · exact recStep_struct g hE h
    · cases h

/-- A successful run of the unification: good, absorbing, moving only variables of the
    equations and new ones. Canonicity is not needed. -/
theorem rLoop_struct {R : RRigid} {P : BVar → Prop} :
    ∀ (fuel : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) (θ' : RBnd) (n' : Nat),
    GoodR R n θ [] [] → EOk θ n E → (∀ w ∈ bvars E, P w) → (∀ w, newB n w = true → P w) →
    rLoop R fuel E X θ n = .ok θ' n' →
    GoodR R n' θ' [] [] ∧ n ≤ n' ∧ AbsS (toRS θ') (toRS θ) ∧ MovesD P (toRS θ) (toRS θ')
  | 0, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | f + 1, [], X, θ, n, θ', n', g, _, _, _, h => by
    simp only [rLoop, ROut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨g, Nat.le_refl _, absS_self g.idem, moves_refl _ _⟩
  | f + 1, (l, r) :: rest, X, θ, n, θ', n', g, hE, hP, hN, h => by
    simp only [rLoop] at h
    split at h
    · rename_i E1 X1 θ1 n1 hs
      have S := uStepR_struct g hE hs
      have hQ : ∀ w, InE ((l, r) :: rest) n w → P w := fun w hw => hw.elim (hP w) (hN w)
      obtain ⟨g2, hn2, ha2, hm2⟩ := rLoop_struct f E1 X1 θ1 n1 θ' n' S.good S.eok (fun w hw => hQ w (S.sub w hw))
        (fun w hw => hN w (by
          cases e : newB n w
          · rw [newB_mono S.le e] at hw; cases hw
          · rfl)) h
      exact ⟨g2, Nat.le_trans S.le hn2, absS_trans ha2 S.abs, moves_trans (moves_mono S.mv hQ) hm2 ha2 S.good.idem⟩
    · cases h

end WDS

end StandardElm.Stat.Complete
