/-
  A Standard Definition of Elm? Mechanisation: the most general unifier with classes and rigid
  variables, milestone (c) of plan step 11 (section 4: (U0) to (U4), (U6); the mgu theorem, parts
  1 to 3; lemmas K1 to K7, K11). Records against records are still `unsupported` (milestone (d)).

  The state is the pending equations, the accumulated substitution `θ` (a binding list, kept
  idempotent and applied to the equations) and a counter `n` of fresh variables (every variable
  of the state is *old*: below `n`). Classes are handled by *refinement*: a flexible variable `β`
  that must also be in `Adm κ` is bound to a fresh variable of class `cls β ⊓ κ` (one step of the
  loop; the equation that asked for it stays first), so that a binding `α ↦ τ` is made only when
  `τ ∈ Adm (cls α)` (`reqC`, MguCls.lean). The steps:

  * (U1) `α ≐ β`, both flexible: the meet `m` of their classes (none: fail); bind the one whose
    class is above `m` to the other, or, when `m` is below both, refine `α` to a fresh `γ` of class
    `m` (the next step binds `β ↦ γ`). One rigid: bind the flexible one to it when the rigid one's
    class is below, else fail. Both rigid: fail.
  * (U2) `α ≐ τ` (τ not a variable): fail if `α` is rigid or occurs in `τ`, or if the requirements
    of `τ` for `cls α` fail (`reqC`), or one of them is on a rigid variable of a class not below
    it, or on a flexible one whose class has no meet with it; refine the first requirement not
    yet met; when all are met, bind `α ↦ τ`.
  * (U3), (U4), (U6) as in Mgu.lean; (U0) drops identical sides.

  Theorems:
  * `cLoop_ok`, `cLoop_fail`: the invariants (I1) (`GoodC`: θ binds only flexible variables, to
    admissible types of their classes, is idempotent, moves no variable of the equations, and
    everything is old) and the solution correspondence (I2), (I3), in the form: a substitution that
    unifies the current problem and absorbs `θ` unifies the original one and absorbs the old `θ`;
    conversely a class-respecting substitution fixing the rigid variables that unifies the old
    problem and absorbs the old `θ` *agrees on the old variables* with one that unifies the new
    problem and absorbs the new `θ` (the factor is extended to the fresh variables);
  * `mguC_ok`, `mguC_fail`: the mgu theorem (section 4, parts 1 and 2);
  * `mguC_terminates`, `mguC_mono` (part 3): the measure is the number of distinct variables of
    the equations, weighted by the height of their classes (any 2, comp and app 1, num and capp 0),
    then the size.
-/
import StandardElmMech.Stat.Complete.MguCls
import StandardElmMech.Stat.Complete.MguTerm

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-! ## Old and new variables -/

/-- A variable created at or above the counter `n`. -/
def _root_.StandardElm.Stat.TyVar.isNew (n : Nat) : TyVar → Bool
  | .fresh k _ => decide (n ≤ k)
  | _ => false

theorem isNew_mono {n m : Nat} (h : n ≤ m) {a : TyVar} (ha : a.isNew n = false) : a.isNew m = false := by
  cases a <;> simp_all [TyVar.isNew]; omega

theorem isNew_fresh_self (n : Nat) (c : Cls) : (TyVar.fresh n c).isNew n = true := by simp [TyVar.isNew]

theorem isNew_fresh_succ (n : Nat) (c : Cls) : (TyVar.fresh n c).isNew (n + 1) = false := by
  simp [TyVar.isNew]

/-- New variables are flexible. -/
def NewFlex (R : Rigid) (n : Nat) : Prop := ∀ a, a.isNew n = true → R a = false

theorem NewFlex.mono {R : Rigid} {n m : Nat} (h : NewFlex R n) (hm : n ≤ m) : NewFlex R m := fun a ha => by
  apply h a
  cases e : a.isNew n
  · rw [isNew_mono hm e] at ha; cases ha
  · rfl

/-- Every variable of the equations is old. -/
def EOld (n : Nat) (E : Eqs) : Prop :=
  ∀ e ∈ E, ∀ a, (BVar.ty a ∈ e.1.vars ∨ BVar.ty a ∈ e.2.vars) → a.isNew n = false

/-- Every key and every variable of an image is old. -/
def BOld (n : Nat) (θ : Bnd) : Prop :=
  ∀ p ∈ θ, p.1.isNew n = false ∧ ∀ b, BVar.ty b ∈ p.2.vars → b.isNew n = false

theorem lk_cases (θ : Bnd) (a : TyVar) : lk θ a = .var a ∨ (a, lk θ a) ∈ θ := by
  unfold lk
  cases hf : FMap.find? θ a with
  | none => exact .inl rfl
  | some τ => exact .inr (find?_some_mem hf)

/-! ## The algorithm -/

inductive COut where
  | ok (θ : Bnd) (n : Nat)
  | fail
  | unsupported
  | outOfFuel
  deriving Repr, DecidableEq

inductive CStep where
  | next (E : Eqs) (θ : Bnd) (n : Nat)
  | fail
  | unsupported

/-- The first requirement not met: `none` = no unifier; `some none` = all met;
    `some (some (β, m))` = refine the flexible `β` to class `m`. -/
def refineTarget (R : Rigid) : List (TyVar × Cls) → Option (Option (TyVar × Cls))
  | [] => some none
  | (b, k) :: rest =>
    if b.cls.le k then refineTarget R rest
    else if R b then none
    else match Cls.meet b.cls k with
      | none => none
      | some m => some (some (b, m))

def bindN (a : TyVar) (τ : Ty) (rest : Eqs) (θ : Bnd) (n : Nat) : CStep :=
  .next (substEqs a τ rest) (bindV a τ θ) n

/-- Refine `b` to the fresh variable `n` of class `m`, in all the equations (`E` includes the
    current one). -/
def refineN (b : TyVar) (m : Cls) (E : Eqs) (θ : Bnd) (n : Nat) : CStep :=
  .next (substEqs b (.var (.fresh n m)) E) (bindV b (.var (.fresh n m)) θ) (n + 1)

/-- (U2) for the flexible `a` against the non-variable `τ`; `cur` is the whole list of
    equations, `rest` the ones after `a ≐ τ`. -/
def varStepC (R : Rigid) (a : TyVar) (τ : Ty) (cur rest : Eqs) (θ : Bnd) (n : Nat) : CStep :=
  if BVar.ty a ∈ τ.vars then .fail else
  match reqC a.cls τ with
  | none => .fail
  | some ps =>
    match refineTarget R ps with
    | none => .fail
    | some none => bindN a τ rest θ n
    | some (some (b, m)) => refineN b m cur θ n

/-- One step on the first equation. -/
def uStepC (R : Rigid) (θ : Bnd) (n : Nat) (l r : Ty) (rest : Eqs) : CStep :=
  if l = r then .next rest θ n else
  match l, r with
  | .var a, .var b =>
    if !R a && !R b then
      match Cls.meet a.cls b.cls with
      | none => .fail
      | some m =>
        if m = b.cls then bindN a (.var b) rest θ n
        else if m = a.cls then bindN b (.var a) rest θ n
        else refineN a m ((.var a, .var b) :: rest) θ n
    else if !R a then (if b.cls.le a.cls then bindN a (.var b) rest θ n else .fail)
    else if !R b then (if a.cls.le b.cls then bindN b (.var a) rest θ n else .fail)
    else .fail
  | .var a, r => if !R a then varStepC R a r ((.var a, r) :: rest) rest θ n else .fail
  | l, .var b => if !R b then varStepC R b l ((l, .var b) :: rest) rest θ n else .fail
  | .fn a b, .fn c d => .next ((a, c) :: (b, d) :: rest) θ n
  | .con as t, .con bs t' =>
    if t = t' ∧ as.length = bs.length then .next (as.zip bs ++ rest) θ n else .fail
  | .record _ _, .record _ _ => .unsupported
  | _, _ => .fail

def cLoop (R : Rigid) : Nat → Eqs → Bnd → Nat → COut
  | 0, _, _, _ => .outOfFuel
  | _ + 1, [], θ, n => .ok θ n
  | f + 1, (l, r) :: rest, θ, n =>
    match uStepC R θ n l r rest with
    | .next E θ' n' => cLoop R f E θ' n'
    | .fail => .fail
    | .unsupported => .unsupported

/-- The unifier of a problem whose variables are below `n`, from the empty substitution. -/
def mguC (fuel : Nat) (R : Rigid) (n : Nat) (E : Eqs) : COut := cLoop R fuel E [] n

/-! ## The invariant (I1) -/

structure GoodC (R : Rigid) (n : Nat) (θ : Bnd) (E : Eqs) : Prop where
  keys : ∀ p ∈ θ, R p.1 = false
  adm : ∀ p ∈ θ, Adm p.1.cls p.2
  idem : Idem (lk θ)
  stable : ∀ e ∈ E, ∀ a, (BVar.ty a ∈ e.1.vars ∨ BVar.ty a ∈ e.2.vars) → lk θ a = .var a
  oldE : EOld n E
  oldθ : BOld n θ

theorem GoodC.fixesR {R : Rigid} {n : Nat} {θ : Bnd} {E : Eqs} (g : GoodC R n θ E) : FixesR R (lk θ) := by
  intro a ha
  rcases lk_cases θ a with h | h
  · exact h
  · have := g.keys _ h; simp only at this; rw [ha] at this; cases this

theorem GoodC.respC {R : Rigid} {n : Nat} {θ : Bnd} {E : Eqs} (g : GoodC R n θ E) : RespC (lk θ) := by
  intro a
  rcases lk_cases θ a with h | h
  · rw [h]; exact admC_self a
  · exact g.adm _ h

/-- The image of an old variable has old variables. -/
theorem GoodC.lk_old {R : Rigid} {n : Nat} {θ : Bnd} {E : Eqs} (g : GoodC R n θ E) {a : TyVar}
    (ha : a.isNew n = false) : ∀ b, BVar.ty b ∈ (lk θ a).vars → b.isNew n = false := by
  rcases lk_cases θ a with h | h
  · rw [h]; intro b hb; simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb; exact ha
  · exact (g.oldθ _ h).2

/-- A new variable is not bound. -/
theorem GoodC.lk_new {R : Rigid} {n : Nat} {θ : Bnd} {E : Eqs} (g : GoodC R n θ E) {a : TyVar}
    (ha : a.isNew n = true) : lk θ a = .var a := by
  rcases lk_cases θ a with h | h
  · exact h
  · have := (g.oldθ _ h).1; simp only at this; rw [ha] at this; cases this

theorem GoodC.mono {R : Rigid} {n m : Nat} {θ : Bnd} {E : Eqs} (g : GoodC R n θ E) (h : n ≤ m) : GoodC R m θ E :=
  ⟨g.keys, g.adm, g.idem, g.stable, fun e he a ha => isNew_mono h (g.oldE e he a ha),
   fun p hp => ⟨isNew_mono h (g.oldθ p hp).1, fun b hb => isNew_mono h ((g.oldθ p hp).2 b hb)⟩⟩

theorem GoodC.tail {R : Rigid} {n : Nat} {θ : Bnd} {e : Ty × Ty} {E : Eqs} (g : GoodC R n θ (e :: E)) :
    GoodC R n θ E :=
  ⟨g.keys, g.adm, g.idem, fun e' he => g.stable e' (.tail _ he), fun e' he => g.oldE e' (.tail _ he), g.oldθ⟩

theorem goodC_nil (R : Rigid) {n : Nat} {E : Eqs} (hE : EOld n E) : GoodC R n [] E :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ _ _ => rfl, fun _ _ _ _ => rfl, hE, fun _ h => (nomatch h)⟩

/-- The solution correspondence (I2) between two states. -/
def CorrC (R : Rigid) (n : Nat) (E : Eqs) (θ : Bnd) (E' : Eqs) (θ' : Bnd) : Prop :=
  (∀ s, Unifies s E' → Absorbs s (lk θ') → Unifies s E ∧ Absorbs s (lk θ)) ∧
  (∀ s, FixesR R s → RespC s → Unifies s E → Absorbs s (lk θ) →
    ∃ s', (∀ a, a.isNew n = false → s' a = s a) ∧ RespC s' ∧ Unifies s' E' ∧ Absorbs s' (lk θ'))

theorem fixesR_of_agree {R : Rigid} {n : Nat} (hN : NewFlex R n) {s s' : FSub} (hs : FixesR R s)
    (ha : ∀ a, a.isNew n = false → s' a = s a) : FixesR R s' := by
  intro a hr
  have : a.isNew n = false := by
    cases e : a.isNew n
    · rfl
    · rw [hN a e] at hr; cases hr
  rw [ha a this, hs a hr]

theorem corrC_refl (R : Rigid) (n : Nat) (E : Eqs) (θ : Bnd) : CorrC R n E θ E θ :=
  ⟨fun _ h1 h2 => ⟨h1, h2⟩, fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, h1, h2⟩⟩

theorem corrC_trans {R : Rigid} {n n1 : Nat} {E E1 E2 : Eqs} {θ θ1 θ2 : Bnd} (hN : NewFlex R n) (hn : n ≤ n1)
    (c1 : CorrC R n E θ E1 θ1) (c2 : CorrC R n1 E1 θ1 E2 θ2) : CorrC R n E θ E2 θ2 := by
  refine ⟨fun s h1 h2 => ?_, fun s hs hr h1 h2 => ?_⟩
  · obtain ⟨a1, a2⟩ := c2.1 s h1 h2; exact c1.1 s a1 a2
  · obtain ⟨s1, ag1, r1, u1, b1⟩ := c1.2 s hs hr h1 h2
    obtain ⟨s2, ag2, r2, u2, b2⟩ := c2.2 s1 (fixesR_of_agree hN hs ag1) r1 u1 b1
    exact ⟨s2, fun a ha => (ag2 a (isNew_mono hn ha)).trans (ag1 a ha), r2, u2, b2⟩

/-! ## A binding (K2), with classes -/

theorem respC_upd {a : TyVar} {τ : Ty} (h : Adm a.cls τ) : RespC (upd a τ) := by
  intro b
  by_cases hb : b = a
  · subst hb; rw [upd_self]; exact h
  · rw [upd_ne τ hb]; exact admC_self b

theorem substEqs_vars {a b : TyVar} {τ : Ty} {rest : Eqs} {e : Ty × Ty} (he : e ∈ substEqs a τ rest)
    (hb : BVar.ty b ∈ e.1.vars ∨ BVar.ty b ∈ e.2.vars) :
    (∃ e0 ∈ rest, (BVar.ty b ∈ e0.1.vars ∨ BVar.ty b ∈ e0.2.vars) ∧ b ≠ a) ∨ BVar.ty b ∈ τ.vars := by
  simp only [substEqs, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rcases hb with hb | hb
  · rcases tyvar_sb_upd hb with ⟨h1, h2⟩ | h1
    · exact .inl ⟨e0, he0, .inl h1, h2⟩
    · exact .inr h1
  · rcases tyvar_sb_upd hb with ⟨h1, h2⟩ | h1
    · exact .inl ⟨e0, he0, .inr h1, h2⟩
    · exact .inr h1

theorem bindC_good {R : Rigid} {n : Nat} {θ : Bnd} {a : TyVar} {τ : Ty} {rest : Eqs}
    (hR : R a = false) (hadm : Adm a.cls τ) (hocc : BVar.ty a ∉ τ.vars)
    (g : GoodC R n θ rest) (ha : lk θ a = .var a) (hτ : ∀ b, BVar.ty b ∈ τ.vars → lk θ b = .var b)
    (haold : a.isNew n = false) (hτold : ∀ b, BVar.ty b ∈ τ.vars → b.isNew n = false) :
    GoodC R n (bindV a τ θ) (substEqs a τ rest) ∧
    ∀ s, (s a = sb s τ ∧ Unifies s rest ∧ Absorbs s (lk θ) ↔
      Unifies s (substEqs a τ rest) ∧ Absorbs s (lk (bindV a τ θ))) := by
  have hlk := lk_bindV (τ := τ) ha
  have fix' : ∀ c, lk θ c = .var c → c ≠ a → lk (bindV a τ θ) c = .var c := by
    intro c hc hca; rw [hlk]; simp only [comp, hc, sb]; exact upd_ne τ hca
  have hτa : ∀ c, BVar.ty c ∈ τ.vars → c ≠ a := fun c hc e => hocc (e ▸ hc)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [bindV, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hR
    · exact g.keys q hq
  · intro p hp
    simp only [bindV, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hadm
    · exact admC_sb (respC_upd hadm) (g.adm q hq)
  · intro b c hcv
    rw [hlk] at hcv; simp only [comp] at hcv
    rcases tyvar_sb_upd hcv with ⟨h1, h2⟩ | h1
    · exact fix' c (g.idem b c h1) h2
    · exact fix' c (hτ c h1) (hτa c h1)
  · intro e he c hcv
    rcases substEqs_vars he hcv with ⟨e0, he0, h1, h2⟩ | h1
    · exact fix' c (g.stable e0 he0 c h1) h2
    · exact fix' c (hτ c h1) (hτa c h1)
  · intro e he c hcv
    rcases substEqs_vars he hcv with ⟨e0, he0, h1, _⟩ | h1
    · exact g.oldE e0 he0 c h1
    · exact hτold c h1
  · intro p hp
    simp only [bindV, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨haold, hτold⟩
    · refine ⟨(g.oldθ q hq).1, fun b hb => ?_⟩
      rcases tyvar_sb_upd hb with ⟨h1, _⟩ | h1
      · exact (g.oldθ q hq).2 b h1
      · exact hτold b h1
  · intro s
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hcs := comp_upd h1
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [substEqs, List.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        simp only [sb_sb, hcs]; exact h2 e0 he0
      · intro b; rw [hlk]; simp only [comp, sb_sb, hcs]; exact h3 b
    · rintro ⟨h2, h3⟩
      have h1 : s a = sb s τ := by
        have := h3 a; rw [hlk] at this; simp only [comp, ha, sb, upd_self] at this; exact this.symm
      have hcs := comp_upd h1
      refine ⟨h1, ?_, ?_⟩
      · intro e he
        have := h2 _ (List.mem_map.mpr ⟨e, he, rfl⟩)
        simp only [sb_sb, hcs] at this; exact this
      · intro b; have := h3 b; rw [hlk] at this; simp only [comp, sb_sb, hcs] at this; exact this

/-- A binding step for the equation `var a ≐ τ` at the head. -/
theorem bind_caseC {R : Rigid} {n : Nat} {θ : Bnd} {a : TyVar} {τ : Ty} {rest : Eqs}
    (hR : R a = false) (hadm : Adm a.cls τ) (hocc : BVar.ty a ∉ τ.vars)
    (g : GoodC R n θ ((.var a, τ) :: rest)) :
    GoodC R n (bindV a τ θ) (substEqs a τ rest) ∧
      CorrC R n ((.var a, τ) :: rest) θ (substEqs a τ rest) (bindV a τ θ) := by
  have hst : ∀ b, (BVar.ty b ∈ (Ty.var a).vars ∨ BVar.ty b ∈ τ.vars) → lk θ b = .var b :=
    g.stable _ (.head _)
  have hold : ∀ b, (BVar.ty b ∈ (Ty.var a).vars ∨ BVar.ty b ∈ τ.vars) → b.isNew n = false :=
    g.oldE _ (.head _)
  obtain ⟨g', hc⟩ := bindC_good hR hadm hocc g.tail (hst a (.inl (mem_vars_var a)))
    (fun b hb => hst b (.inr hb)) (hold a (.inl (mem_vars_var a))) (fun b hb => hold b (.inr hb))
  refine ⟨g', fun s h1 h2 => ?_, fun s _ _ h1 h2 => ⟨s, fun _ _ => rfl, ?_, ?_⟩⟩
  · obtain ⟨e1, e2, e3⟩ := (hc s).mpr ⟨h1, h2⟩
    exact ⟨unifies_cons.mpr ⟨by simp only [sb]; exact e1, e2⟩, e3⟩
  · assumption
  · obtain ⟨u1, u2⟩ := unifies_cons.mp h1
    exact (hc s).mp ⟨by simpa [sb] using u1, u2, h2⟩

theorem bind_caseC' {R : Rigid} {n : Nat} {θ : Bnd} {b : TyVar} {l : Ty} {rest : Eqs}
    (hR : R b = false) (hadm : Adm b.cls l) (hocc : BVar.ty b ∉ l.vars)
    (g : GoodC R n θ ((l, .var b) :: rest)) :
    GoodC R n (bindV b l θ) (substEqs b l rest) ∧
      CorrC R n ((l, .var b) :: rest) θ (substEqs b l rest) (bindV b l θ) := by
  have g' : GoodC R n θ ((.var b, l) :: rest) :=
    ⟨g.keys, g.adm, g.idem, by
      intro e he c hc
      cases he with
      | head => exact g.stable _ (.head _) c hc.symm
      | tail _ he => exact g.stable e (.tail _ he) c hc,
     by
      intro e he c hc
      cases he with
      | head => exact g.oldE _ (.head _) c hc.symm
      | tail _ he => exact g.oldE e (.tail _ he) c hc, g.oldθ⟩
  obtain ⟨g2, c1, c2⟩ := bind_caseC hR hadm hocc g'
  refine ⟨g2, fun s h1 h2 => ?_, fun s hs hr h1 h2 => c2 s hs hr (unifies_swap.mp h1) h2⟩
  obtain ⟨a1, a2⟩ := c1 s h1 h2
  exact ⟨unifies_swap.mp a1, a2⟩

/-! ## A refinement (K6) -/

/-- Refining the flexible old `b` to the fresh `γ = fresh n m` of a class below its own, when
    every unifier gives `b` an image in `Adm m`. -/
theorem refine_caseC {R : Rigid} {n : Nat} {θ : Bnd} {b : TyVar} {m : Cls} {E : Eqs}
    (hR : R b = false) (hm : m.le b.cls = true) (g : GoodC R n θ E)
    (hb : lk θ b = .var b) (hbold : b.isNew n = false)
    (hadm : ∀ s, FixesR R s → RespC s → Unifies s E → Adm m (s b)) :
    GoodC R (n + 1) (bindV b (.var (.fresh n m)) θ) (substEqs b (.var (.fresh n m)) E) ∧
      CorrC R n E θ (substEqs b (.var (.fresh n m)) E) (bindV b (.var (.fresh n m)) θ) := by
  have hγ : ∀ c, BVar.ty c ∈ (Ty.var (.fresh n m)).vars → c = .fresh n m := fun c hc => by
    simpa [Ty.vars] using hc
  have hγnew : (TyVar.fresh n m).isNew n = true := isNew_fresh_self n m
  have hbγ : b ≠ .fresh n m := fun e => by rw [e, hγnew] at hbold; cases hbold
  have g1 := g.mono (Nat.le_succ n)
  obtain ⟨g', hc⟩ := bindC_good (τ := .var (.fresh n m)) hR
    (admC_var_iff.mpr (by simpa [TyVar.cls] using hm))
    (fun h => hbγ (hγ b h)) g1 hb (fun c hc => by rw [hγ c hc]; exact g.lk_new hγnew)
    (isNew_mono (Nat.le_succ n) hbold) (fun c hc => by rw [hγ c hc]; exact isNew_fresh_succ n m)
  refine ⟨g', fun s h1 h2 => ?_, fun s hs hr h1 h2 => ?_⟩
  · obtain ⟨_, e2, e3⟩ := (hc s).mpr ⟨h1, h2⟩; exact ⟨e2, e3⟩
  · let s' : FSub := fun c => if c = .fresh n m then s b else s c
    have ag : ∀ c, c.isNew n = false → s' c = s c := fun c hc => by
      simp only [s']; rw [if_neg]; rintro rfl; rw [hγnew] at hc; cases hc
    have agT : ∀ τ : Ty, (∀ c, BVar.ty c ∈ τ.vars → c.isNew n = false) → sb s' τ = sb s τ :=
      fun τ hτ => sb_congr τ fun c hc => ag c (hτ c hc)
    refine ⟨s', ag, fun c => ?_, (hc s').mp ⟨?_, ?_, ?_⟩⟩
    · simp only [s']
      split
      · rename_i e; subst e; exact hadm s hs hr h1
      · exact hr c
    · simp only [sb, s', if_pos rfl]; rw [if_neg hbγ]
    · intro e he
      rw [agT _ (fun c hc => g.oldE e he c (.inl hc)), agT _ (fun c hc => g.oldE e he c (.inr hc))]
      exact h1 e he
    · intro c
      by_cases hcn : c.isNew n = true
      · rw [g.lk_new hcn]; rfl
      · have hco : c.isNew n = false := by simpa using hcn
        rw [agT _ (g.lk_old hco), ag c hco]; exact h2 c

/-! ## Requirements: the first one not met -/

theorem refineTarget_none {R : Rigid} : ∀ {ps : List (TyVar × Cls)}, refineTarget R ps = none →
    ∃ p ∈ ps, p.1.cls.le p.2 = false ∧ (R p.1 = true ∨ Cls.meet p.1.cls p.2 = none)
  | [], h => by cases h
  | (b, k) :: rest, h => by
    simp only [refineTarget] at h
    split at h
    · obtain ⟨p, hp, h1⟩ := refineTarget_none h; exact ⟨p, .tail _ hp, h1⟩
    · rename_i hle
      split at h
      · rename_i hr; exact ⟨(b, k), .head _, by simpa using hle, .inl hr⟩
      · split at h
        · rename_i hm; exact ⟨(b, k), .head _, by simpa using hle, .inr hm⟩
        · cases h

theorem refineTarget_all {R : Rigid} : ∀ {ps : List (TyVar × Cls)}, refineTarget R ps = some none →
    ∀ p ∈ ps, p.1.cls.le p.2 = true
  | [], _ => fun _ h => by cases h
  | (b, k) :: rest, h => by
    simp only [refineTarget] at h
    split at h
    · rename_i hle
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hle
      · exact refineTarget_all h p hp
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h

theorem refineTarget_some {R : Rigid} : ∀ {ps : List (TyVar × Cls)} {b : TyVar} {m : Cls},
    refineTarget R ps = some (some (b, m)) →
    ∃ k, (b, k) ∈ ps ∧ R b = false ∧ Cls.meet b.cls k = some m ∧ b.cls.le k = false
  | [], _, _, h => by cases h
  | (b', k) :: rest, b, m, h => by
    simp only [refineTarget] at h
    split at h
    · obtain ⟨k', hk, h1⟩ := refineTarget_some h; exact ⟨k', .tail _ hk, h1⟩
    · rename_i hle
      split at h
      · cases h
      · rename_i hr
        split at h
        · cases h
        · rename_i m' hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨k, .head _, by simpa using hr, hm, by simpa using hle⟩

/-- When every requirement is met, the type is admissible. -/
theorem adm_of_req {k : Cls} {τ : Ty} {ps : List (TyVar × Cls)} (h : reqC k τ = some ps)
    (hall : ∀ p ∈ ps, p.1.cls.le p.2 = true) : Adm k τ := by
  have := (reqC_spec idS k τ ps h).mpr fun p hp => admC_var_iff.mpr (hall p hp)
  rwa [sb_id] at this

/-- The meet is strictly below: a refinement lowers the class. -/
theorem meet_lt {b k m : Cls} (hm : Cls.meet b k = some m) (hle : b.le k = false) : m.le b = true ∧ m ≠ b := by
  obtain ⟨h1, h2, _⟩ := (Cls.meet_spec b k m).mp hm
  refine ⟨h1, fun e => ?_⟩
  subst e; rw [h2] at hle; cases hle

/-! ## One step -/

theorem stable_consC {R : Rigid} {n : Nat} {θ : Bnd} {l r : Ty} {rest : Eqs} (g : GoodC R n θ ((l, r) :: rest)) :
    (∀ b, BVar.ty b ∈ l.vars → lk θ b = .var b) ∧ (∀ b, BVar.ty b ∈ r.vars → lk θ b = .var b) ∧
    (∀ b, BVar.ty b ∈ l.vars → b.isNew n = false) ∧ (∀ b, BVar.ty b ∈ r.vars → b.isNew n = false) :=
  ⟨fun b h => g.stable _ (.head _) b (.inl h), fun b h => g.stable _ (.head _) b (.inr h),
   fun b h => g.oldE _ (.head _) b (.inl h), fun b h => g.oldE _ (.head _) b (.inr h)⟩

/-- The steps of (U2) for `var a ≐ τ` (τ not a variable). -/
theorem varStepC_next {R : Rigid} {n : Nat} {θ : Bnd} {a : TyVar} {τ : Ty} {cur rest E' : Eqs} {θ' : Bnd}
    {n' : Nat} (hR : R a = false) (g : GoodC R n θ cur) (hcur : ∀ s, Unifies s cur → s a = sb s τ)
    (hτc : ∀ c, BVar.ty c ∈ τ.vars → lk θ c = .var c ∧ c.isNew n = false)
    (gb : ∀ (ha : Adm a.cls τ) (hocc : BVar.ty a ∉ τ.vars),
      GoodC R n (bindV a τ θ) (substEqs a τ rest) ∧ CorrC R n cur θ (substEqs a τ rest) (bindV a τ θ))
    (h : varStepC R a τ cur rest θ n = .next E' θ' n') :
    GoodC R n' θ' E' ∧ n ≤ n' ∧ CorrC R n cur θ E' θ' := by
  unfold varStepC at h
  split at h
  · cases h
  · rename_i hocc
    split at h
    · cases h
    · rename_i ps hps
      split at h
      · cases h
      · cases h
        exact ⟨(gb (adm_of_req hps (refineTarget_all (by assumption))) hocc).1, Nat.le_refl _,
          (gb (adm_of_req hps (refineTarget_all (by assumption))) hocc).2⟩
      · rename_i b m ht
        cases h
        obtain ⟨k, hk, hRb, hm, hle⟩ := refineTarget_some ht
        have hbτ : BVar.ty b ∈ τ.vars := reqC_vars _ _ _ hps _ hk
        obtain ⟨g', c⟩ := refine_caseC hRb (meet_lt hm hle).1 g
          (hτc b hbτ).1 (hτc b hbτ).2 (by
            intro s hs hr hu
            have e := hcur s hu
            have h1 : Adm a.cls (sb s τ) := e ▸ hr a
            have h2 := (reqC_spec s _ _ _ hps).mp h1 _ hk
            obtain ⟨m', hm', hadm⟩ := admC_meet (hr b) h2
            rw [hm] at hm'; cases hm'; exact hadm)
        exact ⟨g', Nat.le_succ n, c⟩

theorem uStepC_next {R : Rigid} {n : Nat} {θ : Bnd} {l r : Ty} {rest E' : Eqs} {θ' : Bnd} {n' : Nat}
    (g : GoodC R n θ ((l, r) :: rest)) (h : uStepC R θ n l r rest = .next E' θ' n') :
    GoodC R n' θ' E' ∧ n ≤ n' ∧ CorrC R n ((l, r) :: rest) θ E' θ' := by
  unfold uStepC at h
  split at h
  · rename_i hlr
    cases h; subst hlr
    refine ⟨g.tail, Nat.le_refl _, fun s h1 h2 => ⟨unifies_cons.mpr ⟨rfl, h1⟩, h2⟩,
      fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, (unifies_cons.mp h1).2, h2⟩⟩
  · obtain ⟨hl, hr, ol, or⟩ := stable_consC g
    split at h
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
          · rename_i e; subst e; cases h
            obtain ⟨g', c⟩ := bind_caseC hfl.1 (admC_var_iff.mpr hma) nab g
            exact ⟨g', Nat.le_refl _, c⟩
          · split at h
            · rename_i _ e; subst e; cases h
              obtain ⟨g', c⟩ := bind_caseC' hfl.2 (admC_var_iff.mpr hmb) nba g
              exact ⟨g', Nat.le_refl _, c⟩
            · cases h
              obtain ⟨g', c⟩ := refine_caseC hfl.1 hma g (hl a (mem_vars_var a)) (ol a (mem_vars_var a))
                (by
                  intro s _ hr' hu
                  have e : s a = s b := by simpa [sb] using (unifies_cons.mp hu).1
                  obtain ⟨m', hm', hadm⟩ := admC_meet (hr' a) (e ▸ hr' b)
                  rw [hm] at hm'; cases hm'; exact hadm)
              exact ⟨g', Nat.le_succ n, c⟩
      · split at h
        · rename_i hra
          simp only [Bool.not_eq_true'] at hra
          split at h
          · rename_i hle; cases h
            obtain ⟨g', c⟩ := bind_caseC hra (admC_var_iff.mpr hle) nab g
            exact ⟨g', Nat.le_refl _, c⟩
          · cases h
        · split at h
          · rename_i _ hrb
            simp only [Bool.not_eq_true'] at hrb
            split at h
            · rename_i hle; cases h
              obtain ⟨g', c⟩ := bind_caseC' hrb (admC_var_iff.mpr hle) nba g
              exact ⟨g', Nat.le_refl _, c⟩
            · cases h
          · cases h
    · -- var, non-var
      rename_i a r' _ _
      split at h
      · rename_i hra
        simp only [Bool.not_eq_true'] at hra
        exact varStepC_next hra g (fun s hu => by simpa [sb] using (unifies_cons.mp hu).1)
          (fun c hc => ⟨hr c hc, or c hc⟩) (fun ha hocc => bind_caseC hra ha hocc g) h
      · cases h
    · -- non-var, var
      rename_i l' b _ _
      split at h
      · rename_i hrb
        simp only [Bool.not_eq_true'] at hrb
        exact varStepC_next hrb g (fun s hu => by simpa [sb] using (unifies_cons.mp hu).1.symm)
          (fun c hc => ⟨hl c hc, ol c hc⟩) (fun ha hocc => bind_caseC' hrb ha hocc g) h
      · cases h
    · -- fn, fn
      cases h
      refine ⟨⟨g.keys, g.adm, g.idem, ?_, ?_, g.oldθ⟩, Nat.le_refl _, ?_, ?_⟩
      · intro e he x hx
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · rcases hx with hx | hx
          · exact hl x (by simp [Ty.vars, hx])
          · exact hr x (by simp [Ty.vars, hx])
        · rcases hx with hx | hx
          · exact hl x (by simp [Ty.vars, hx])
          · exact hr x (by simp [Ty.vars, hx])
        · exact g.stable e (.tail _ he) x hx
      · intro e he x hx
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · rcases hx with hx | hx
          · exact ol x (by simp [Ty.vars, hx])
          · exact or x (by simp [Ty.vars, hx])
        · rcases hx with hx | hx
          · exact ol x (by simp [Ty.vars, hx])
          · exact or x (by simp [Ty.vars, hx])
        · exact g.oldE e (.tail _ he) x hx
      · intro s h1 h2
        refine ⟨?_, h2⟩
        simp only [unifies_cons, sb, Ty.fn.injEq] at h1 ⊢
        exact ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩
      · intro s _ hr' h1 h2
        refine ⟨s, fun _ _ => rfl, hr', ?_, h2⟩
        simp only [unifies_cons, sb, Ty.fn.injEq] at h1 ⊢
        exact ⟨h1.1.1, h1.1.2, h1.2⟩
    · -- con, con
      split at h
      · rename_i as t bs t' hc
        obtain ⟨rfl, hlen⟩ := hc
        cases h
        have memL : ∀ {τ : Ty} {l : List Ty} {v : BVar}, τ ∈ l → v ∈ τ.vars → v ∈ Ty.listVars l :=
          fun hm hv => uStep_next.listVars_of_mem hm hv
        refine ⟨⟨g.keys, g.adm, g.idem, ?_, ?_, g.oldθ⟩, Nat.le_refl _, ?_, ?_⟩
        · intro e he x hx
          rcases List.mem_append.mp he with he | he
          · have hm := List.of_mem_zip he
            rcases hx with hx | hx
            · exact hl x (by simp only [Ty.vars]; exact memL hm.1 hx)
            · exact hr x (by simp only [Ty.vars]; exact memL hm.2 hx)
          · exact g.stable e (.tail _ he) x hx
        · intro e he x hx
          rcases List.mem_append.mp he with he | he
          · have hm := List.of_mem_zip he
            rcases hx with hx | hx
            · exact ol x (by simp only [Ty.vars]; exact memL hm.1 hx)
            · exact or x (by simp only [Ty.vars]; exact memL hm.2 hx)
          · exact g.oldE e (.tail _ he) x hx
        · intro s h1 h2
          rw [unifies_append, unifies_zip hlen] at h1
          exact ⟨unifies_cons.mpr ⟨by simp only [sb, h1.1], h1.2⟩, h2⟩
        · intro s _ hr' h1 h2
          refine ⟨s, fun _ _ => rfl, hr', ?_, h2⟩
          rw [unifies_append, unifies_zip hlen]
          obtain ⟨u1, u2⟩ := unifies_cons.mp h1
          simp only [sb, Ty.con.injEq] at u1
          exact ⟨u1.1, u2⟩
      · cases h
    · cases h
    · cases h

end StandardElm.Stat.Complete
