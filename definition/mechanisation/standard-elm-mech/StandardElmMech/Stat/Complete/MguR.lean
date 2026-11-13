/-
  A Standard Definition of Elm? Mechanisation: unification with classes, rigid variables and
  *rows*, milestone (d) of plan step 11 (section 4: (U0) to (U6), the row case (U5) with lacks
  sets, Rémy style, A23; K1 to K11).

  The state is the pending equations `E`, the *frame* `X` (types on which every unifier must be
  defined: section 2), the accumulated substitution `θ` (a binding list of type and row variables,
  `RBnd`, idempotent and applied to `E` and `X`) and the counter `n`. Rigid variables (type or row)
  are given by `R : BVar → Bool`. A unifier of `(E, X)` (`UniR`) equalises the equations and has a
  *canonical* image on every type of the problem (`cnB`): it is defined on them in the sense of
  A23 (RSubst.lean, K9). The steps (`uStepR`):

  * (U0) identical sides: dropped; (U1), (U2), (U3), (U4), (U6) as MguC.lean, with substitutions
    of type and row variables (`rsb`); the occurs check `α ∈ vars τ` sees field types and tails.
  * (U5) records `⟨ρ1 | t1⟩ ≐ ⟨ρ2 | t2⟩` (`recStep`): the equations of the common fields
    (`commonEqs`), and, with `o1`, `o2` the fields each side has and the other lacks (`onlyL`), the
    cases of section 4: both closed (fail unless `o1 = o2 = ∅`); one closed (bind the other's tail
    to the missing fields, closed); the same tail (fail unless `o1 = o2 = ∅`); different tails (bind
    one to the other, or a tail to the other side's missing fields and tail, or both tails to the
    missing fields and one fresh tail `ε`, the second binding after the first).
  * A row binding `e ↦ ⟨ϱ | t⟩` (`bindRow`) fails if `e` is rigid, occurs in `⟨ϱ | t⟩` (the occurs
    check through rows), or a label of `ϱ` is in `lacks(e)` over the frame and the equations
    (`lacksIn`): every row that `e` extends in the problem.

  A step that consumes an equation puts its left side in the frame: the problem keeps the types
  whose definedness the unifiers must have.

  This file: the algorithm, the invariant (I1) `GoodR` and the solution correspondence (I2)
  `CorrR`, a binding (K2, K9) and a class refinement (K6). The record step is MguRRec.lean; the
  loop, the mgu theorem and termination are MguRLoop.lean.
-/
import StandardElmMech.Stat.Complete.RSubst
import StandardElmMech.Stat.Complete.MguC

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-- Rigid variables, type or row. -/
abbrev RRigid := BVar → Bool

/-- A variable created at or above the counter `n`. -/
def newB (n : Nat) : BVar → Bool
  | .ty a => a.isNew n
  | .row (.fresh k) => decide (n ≤ k)
  | .row _ => false

theorem newB_mono {n m : Nat} (h : n ≤ m) {v : BVar} (hv : newB n v = false) : newB m v = false := by
  cases v with
  | ty a => exact isNew_mono h hv
  | row e => cases e <;> simp_all [newB]; omega

/-- The types of a problem: the frame and both sides of every equation. -/
def tys (E : Eqs) (X : List Ty) : List Ty := X ++ E.flatMap fun e => [e.1, e.2]

def sE (σ : RSub) (E : Eqs) : Eqs := E.map fun e => (rsb σ e.1, rsb σ e.2)
def sX (σ : RSub) (X : List Ty) : List Ty := X.map (rsb σ)

/-- `lacks_{X ∪ E}(e)`. -/
def lacksIn (e : RowVar) (E : Eqs) (X : List Ty) : List Lab := (tys E X).flatMap (lacksOf e)

/-- The fields of `ρ1` whose labels `ρ2` lacks. -/
def onlyL (ρ1 ρ2 : Row) : Row := ρ1.filter fun p => !decide (p.1 ∈ labs ρ2)

/-- The equations of the common fields, in the order of `ρ1`. -/
def commonEqs (ρ1 ρ2 : Row) : Eqs := ρ1.filterMap fun p => (FMap.find? ρ2 p.1).map fun τ => (p.2, τ)

/-! ## The algorithm -/

inductive RStep where
  | next (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat)
  | fail

inductive ROut where
  | ok (θ : RBnd) (n : Nat)
  | fail
  | outOfFuel
  deriving Repr, DecidableEq

/-- Bind `v ↦ τ` in the equations, the frame and the accumulated substitution. -/
def bindS (v : BVar) (τ : Ty) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) : RStep :=
  .next (sE (one v τ) E) (sX (one v τ) X) (bindR v τ θ) n

/-- Refine the type variable `b` to the fresh `γ = fresh n m`. -/
def refineS (b : TyVar) (m : Cls) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) : RStep :=
  bindS (.ty b) (.var (.fresh n m)) E X θ (n + 1)

/-- Bind the row variable `e` to `⟨ϱ | t⟩`: fail if `e` is rigid, occurs in `⟨ϱ | t⟩`, or must
    lack a label of `ϱ` (A23). -/
def bindRow (R : RRigid) (e : RowVar) (ϱ : Row) (t : Option RowVar) (E : Eqs) (X : List Ty) (θ : RBnd)
    (n : Nat) : RStep :=
  if R (.row e) then .fail
  else if BVar.row e ∈ (Ty.record ϱ t).vars then .fail
  else if (labs ϱ).any (fun l => decide (l ∈ lacksIn e E X)) then .fail
  else bindS (.row e) (.record ϱ t) E X θ n

/-- (U5): `⟨ρ1 | t1⟩ ≐ ⟨ρ2 | t2⟩`, the equation removed (`rest` the others, `X` the frame with its
    left side). -/
def recStep (R : RRigid) (ρ1 : Row) (t1 : Option RowVar) (ρ2 : Row) (t2 : Option RowVar)
    (rest : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) : RStep :=
  let F := commonEqs ρ1 ρ2 ++ rest
  let o1 := onlyL ρ1 ρ2
  let o2 := onlyL ρ2 ρ1
  match t1, t2 with
  | none, none => if o1 = [] ∧ o2 = [] then .next F X θ n else .fail
  | none, some e2 => if o2 = [] then bindRow R e2 o1 none F X θ n else .fail
  | some e1, none => if o1 = [] then bindRow R e1 o2 none F X θ n else .fail
  | some e1, some e2 =>
    if e1 = e2 then (if o1 = [] ∧ o2 = [] then .next F X θ n else .fail)
    else if o2 = [] then
      (if o1 = [] then
        (if !R (.row e1) then bindRow R e1 [] (some e2) F X θ n else bindRow R e2 [] (some e1) F X θ n)
       else bindRow R e2 o1 (some e1) F X θ n)
    else if o1 = [] then bindRow R e1 o2 (some e2) F X θ n
    else
      match bindRow R e1 o2 (some (.fresh n)) F X θ (n + 1) with
      | .next F' X' θ' n' =>
        bindRow R e2 (rsbRow (one (.row e1) (.record o2 (some (.fresh n)))) o1) (some (.fresh n)) F' X' θ' n'
      | .fail => .fail

/-- (U2) for the flexible `a` against the non-variable `τ`; `cur` is the whole list of equations,
    `rest` the ones after `a ≐ τ`. -/
def varStepR (R : RRigid) (a : TyVar) (τ : Ty) (cur rest : Eqs) (X : List Ty) (θ : RBnd) (n : Nat) : RStep :=
  if BVar.ty a ∈ τ.vars then .fail else
  match reqC a.cls τ with
  | none => .fail
  | some ps =>
    match refineTarget (fun b => R (.ty b)) ps with
    | none => .fail
    | some none => bindS (.ty a) τ rest (.var a :: X) θ n
    | some (some (b, m)) => refineS b m cur X θ n

/-- One step on the first equation. -/
def uStepR (R : RRigid) (θ : RBnd) (n : Nat) (l r : Ty) (rest : Eqs) (X : List Ty) : RStep :=
  if l = r then .next rest (l :: X) θ n else
  match l, r with
  | .var a, .var b =>
    if !R (.ty a) && !R (.ty b) then
      match Cls.meet a.cls b.cls with
      | none => .fail
      | some m =>
        if m = b.cls then bindS (.ty a) (.var b) rest (.var a :: X) θ n
        else if m = a.cls then bindS (.ty b) (.var a) rest (.var a :: X) θ n
        else refineS a m ((.var a, .var b) :: rest) X θ n
    else if !R (.ty a) then (if b.cls.le a.cls then bindS (.ty a) (.var b) rest (.var a :: X) θ n else .fail)
    else if !R (.ty b) then (if a.cls.le b.cls then bindS (.ty b) (.var a) rest (.var a :: X) θ n else .fail)
    else .fail
  | .var a, r => if !R (.ty a) then varStepR R a r ((.var a, r) :: rest) rest X θ n else .fail
  | l, .var b => if !R (.ty b) then varStepR R b l ((l, .var b) :: rest) rest X θ n else .fail
  | .fn a b, .fn c d => .next ((a, c) :: (b, d) :: rest) X θ n
  | .con as t, .con bs t' =>
    if t = t' ∧ as.length = bs.length then .next (as.zip bs ++ rest) X θ n else .fail
  | .record ρ1 t1, .record ρ2 t2 => recStep R ρ1 t1 ρ2 t2 rest (.record ρ1 t1 :: X) θ n
  | _, _ => .fail

def rLoop (R : RRigid) : Nat → Eqs → List Ty → RBnd → Nat → ROut
  | 0, _, _, _, _ => .outOfFuel
  | _ + 1, [], _, θ, n => .ok θ n
  | f + 1, (l, r) :: rest, X, θ, n =>
    match uStepR R θ n l r rest X with
    | .next E X' θ' n' => rLoop R f E X' θ' n'
    | .fail => .fail

/-- The unifier of a problem `(E, X)` whose variables are below `n`. -/
def mguR (fuel : Nat) (R : RRigid) (n : Nat) (E : Eqs) (X : List Ty) : ROut := rLoop R fuel E X [] n

/-! ## Unifiers, absorption, the invariant -/

/-- A unifier of `(E, X)`: it equalises the equations and is defined (canonical) on every type. -/
def UniR (s : RSub) (E : Eqs) (X : List Ty) : Prop :=
  (∀ e ∈ E, rsb s e.1 = rsb s e.2) ∧ ∀ τ ∈ tys E X, cnB (rsb s τ) = true

/-- `s ∘ θ = s`. -/
def AbsR (s : RSub) (θ : RBnd) : Prop := ∀ v, rsb s ((toRS θ).img v) = s.img v

def FixR (R : RRigid) (s : RSub) : Prop := ∀ v, R v = true → s.img v = vty v

structure GoodR (R : RRigid) (n : Nat) (θ : RBnd) (E : Eqs) (X : List Ty) : Prop where
  keys : ∀ p ∈ θ, R p.1 = false
  adm : ∀ p ∈ θ, ∀ a, p.1 = .ty a → Adm a.cls p.2
  rrec : RowRec θ
  idem : ∀ v, ∀ w ∈ ((toRS θ).img v).vars, (toRS θ).img w = vty w
  stable : ∀ τ ∈ tys E X, ∀ w ∈ τ.vars, (toRS θ).img w = vty w
  old : ∀ τ ∈ tys E X, ∀ w ∈ τ.vars, newB n w = false
  oldθ : ∀ p ∈ θ, newB n p.1 = false ∧ ∀ w ∈ p.2.vars, newB n w = false
  cn : ∀ τ ∈ tys E X, cnB τ = true

/-- The solution correspondence (I2). -/
def CorrR (R : RRigid) (n : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (E' : Eqs) (X' : List Ty) (θ' : RBnd) : Prop :=
  (∀ s, UniR s E' X' → AbsR s θ' → UniR s E X ∧ AbsR s θ) ∧
  (∀ s, FixR R s → RespR s → UniR s E X → AbsR s θ →
    ∃ s', (∀ v, newB n v = false → s'.img v = s.img v) ∧ RespR s' ∧ UniR s' E' X' ∧ AbsR s' θ')

/-- New variables are flexible. -/
def NewFlexR (R : RRigid) (n : Nat) : Prop := ∀ v, newB n v = true → R v = false

theorem NewFlexR.mono {R : RRigid} {n m : Nat} (h : NewFlexR R n) (hm : n ≤ m) : NewFlexR R m := fun v hv => by
  apply h v
  cases e : newB n v
  · rw [newB_mono hm e] at hv; cases hv
  · rfl

theorem fixR_of_agree {R : RRigid} {n : Nat} (hN : NewFlexR R n) {s s' : RSub} (hs : FixR R s)
    (ha : ∀ v, newB n v = false → s'.img v = s.img v) : FixR R s' := by
  intro v hr
  have : newB n v = false := by
    cases e : newB n v
    · rfl
    · rw [hN v e] at hr; cases hr
  rw [ha v this, hs v hr]

theorem corrR_refl (R : RRigid) (n : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) : CorrR R n E X θ E X θ :=
  ⟨fun _ h1 h2 => ⟨h1, h2⟩, fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, h1, h2⟩⟩

theorem corrR_trans {R : RRigid} {n n1 : Nat} {E E1 E2 : Eqs} {X X1 X2 : List Ty} {θ θ1 θ2 : RBnd}
    (hN : NewFlexR R n) (hn : n ≤ n1)
    (c1 : CorrR R n E X θ E1 X1 θ1) (c2 : CorrR R n1 E1 X1 θ1 E2 X2 θ2) : CorrR R n E X θ E2 X2 θ2 := by
  refine ⟨fun s h1 h2 => ?_, fun s hs hr h1 h2 => ?_⟩
  · obtain ⟨a1, a2⟩ := c2.1 s h1 h2; exact c1.1 s a1 a2
  · obtain ⟨s1, ag1, r1, u1, b1⟩ := c1.2 s hs hr h1 h2
    obtain ⟨s2, ag2, r2, u2, b2⟩ := c2.2 s1 (fixR_of_agree hN hs ag1) r1 u1 b1
    exact ⟨s2, fun v hv => (ag2 v (newB_mono hn hv)).trans (ag1 v hv), r2, u2, b2⟩

/-! ## The types of a problem -/

theorem mem_tys {τ : Ty} {E : Eqs} {X : List Ty} : τ ∈ tys E X ↔ τ ∈ X ∨ ∃ e ∈ E, τ = e.1 ∨ τ = e.2 := by
  simp only [tys, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem tys_cons {τ l r : Ty} {E : Eqs} {X : List Ty} :
    τ ∈ tys ((l, r) :: E) X ↔ τ = l ∨ τ = r ∨ τ ∈ tys E X := by
  simp only [mem_tys, List.mem_cons, exists_eq_or_imp]
  constructor
  · rintro (h | (h | h) | h)
    · exact .inr (.inr (.inl h))
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  · rintro (h | h | h | h)
    · exact .inr (.inl (.inl h))
    · exact .inr (.inl (.inr h))
    · exact .inl h
    · exact .inr (.inr h)

theorem tys_frame_cons {τ x : Ty} {E : Eqs} {X : List Ty} : τ ∈ tys E (x :: X) ↔ τ = x ∨ τ ∈ tys E X := by
  simp only [mem_tys, List.mem_cons, or_assoc]

theorem tys_append {τ : Ty} {E F : Eqs} {X : List Ty} : τ ∈ tys (E ++ F) X ↔ τ ∈ tys F X ∨ ∃ e ∈ E, τ = e.1 ∨ τ = e.2 := by
  simp only [mem_tys, List.mem_append]
  constructor
  · rintro (h | ⟨e, he | he, h⟩)
    · exact .inl (.inl h)
    · exact .inr ⟨e, he, h⟩
    · exact .inl (.inr ⟨e, he, h⟩)
  · rintro ((h | ⟨e, he, h⟩) | ⟨e, he, h⟩)
    · exact .inl h
    · exact .inr ⟨e, .inr he, h⟩
    · exact .inr ⟨e, .inl he, h⟩

theorem tys_subst {σ : RSub} {E : Eqs} {X : List Ty} {τ : Ty} :
    τ ∈ tys (sE σ E) (sX σ X) ↔ ∃ τ0 ∈ tys E X, τ = rsb σ τ0 := by
  simp only [mem_tys, sE, sX, List.mem_map]
  constructor
  · rintro (⟨τ0, h, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, h | h⟩)
    · exact ⟨τ0, .inl h, rfl⟩
    · exact ⟨e.1, .inr ⟨e, he, .inl rfl⟩, h⟩
    · exact ⟨e.2, .inr ⟨e, he, .inr rfl⟩, h⟩
  · rintro ⟨τ0, h | ⟨e, he, h | h⟩, rfl⟩
    · exact .inl ⟨τ0, h, rfl⟩
    · subst h; exact .inr ⟨_, ⟨e, he, rfl⟩, .inl rfl⟩
    · subst h; exact .inr ⟨_, ⟨e, he, rfl⟩, .inr rfl⟩

theorem uniR_cons {s : RSub} {l r : Ty} {E : Eqs} {X : List Ty} :
    UniR s ((l, r) :: E) X ↔ rsb s l = rsb s r ∧ UniR s E (l :: X) ∧ cnB (rsb s r) = true := by
  simp only [UniR, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ⟨h2, fun τ hτ => ?_⟩, h3 r (tys_cons.mpr (.inr (.inl rfl)))⟩
    rcases tys_frame_cons.mp hτ with rfl | hτ
    · exact h3 _ (tys_cons.mpr (.inl rfl))
    · exact h3 τ (tys_cons.mpr (.inr (.inr hτ)))
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨⟨h1, h2⟩, fun τ hτ => ?_⟩
    rcases tys_cons.mp hτ with rfl | rfl | hτ
    · exact h3 _ (tys_frame_cons.mpr (.inl rfl))
    · exact h4
    · exact h3 τ (tys_frame_cons.mpr (.inr hτ))

/-- A canonical image of a type that is in the frame. -/
theorem uniR_frame {s : RSub} {E : Eqs} {X : List Ty} {x : Ty} (h : UniR s E (x :: X)) : cnB (rsb s x) = true :=
  h.2 x (tys_frame_cons.mpr (.inl rfl))

/-! ## Absorption -/

/-- K2: `s` absorbs the binding `v ↦ τ` when `s v = s τ`. -/
theorem rcomp_one {s : RSub} {v : BVar} {τ : Ty} (hv : IsRec v τ) (h : s.img v = rsb s τ) :
    rcomp s (one v τ) = s := by
  refine RSub.eq_of_img fun w => ?_
  rw [img_rcomp]
  by_cases hw : w = v
  · subst hw; rw [img_one_self hv, h]
  · rw [img_one_ne τ hw, rsb_vty]

theorem absR_iff {s : RSub} {θ : RBnd} : AbsR s θ ↔ rcomp s (toRS θ) = s :=
  ⟨fun h => RSub.eq_of_img fun v => by rw [img_rcomp]; exact h v,
   fun h v => by rw [← img_rcomp, h]⟩

theorem rsb_absorb {s σ : RSub} (h : rcomp s σ = s) (τ : Ty) : rsb s (rsb σ τ) = rsb s τ := by
  rw [rsb_rsb, h]

theorem uniR_absorb {s σ : RSub} (h : rcomp s σ = s) {E : Eqs} {X : List Ty} :
    UniR s (sE σ E) (sX σ X) ↔ UniR s E X := by
  simp only [UniR]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
    · have := h1 _ (List.mem_map.mpr ⟨e, he, rfl⟩); simp only [rsb_absorb h] at this; exact this
    · have := h2 _ (tys_subst.mpr ⟨τ, hτ, rfl⟩); rw [rsb_absorb h] at this; exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he => ?_, fun τ hτ => ?_⟩
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he; simp only [rsb_absorb h]; exact h1 e0 he0
    · obtain ⟨τ0, hτ0, rfl⟩ := tys_subst.mp hτ; rw [rsb_absorb h]; exact h2 τ0 hτ0

/-! ## A binding (K2, K9, with classes and rows) -/

theorem vars_rsb_one {v w : BVar} {τ σ : Ty} (h : w ∈ (rsb (one v τ) σ).vars) (hv : IsRec v τ) :
    (w ∈ σ.vars ∧ w ≠ v) ∨ w ∈ τ.vars := by
  obtain ⟨w', hw', hw⟩ := (mem_vars_rsb _ σ w).mp h
  by_cases e : w' = v
  · subst e; rw [img_one_self hv] at hw; exact .inr hw
  · rw [img_one_ne τ e, vars_vty, List.mem_singleton] at hw; subst hw; exact .inl ⟨hw', e⟩

theorem respR_one {v : BVar} {τ : Ty} (h : ∀ a, v = .ty a → Adm a.cls τ) : RespR (one v τ) := by
  intro a
  by_cases e : BVar.ty a = v
  · subst e
    have := img_one_self (v := BVar.ty a) (σ := τ) trivial
    simp only [RSub.img] at this; rw [this]; exact h a rfl
  · have := img_one_ne (v := v) τ e; simp only [RSub.img, vty] at this; rw [this]; exact admC_self a

/-- The canonical image of a canonical type under one binding that passes the lacks check. -/
theorem cn_one {v : BVar} {τ σ : Ty} (hv : IsRec v τ) (hτ : cnB τ = true) (hσ : cnB σ = true)
    (hl : ∀ e, v = .row e → ∀ l ∈ lacksOf e σ, l ∉ labs (rowOf τ).1) : cnB (rsb (one v τ) σ) = true := by
  refine cn_rsb hσ (fun w _ => ?_) (fun e l hle => ?_)
  · by_cases e : w = v
    · subst e; rw [img_one_self hv]; exact hτ
    · rw [img_one_ne τ e]; exact cnB_vty w
  · by_cases ev : BVar.row e = v
    · subst ev
      have := hl e rfl l hle
      simp only [one, toRS, FMap.find?, if_pos rfl]; exact this
    · have := img_one_ne (v := v) τ ev
      simp only [RSub.img, vty, Ty.record.injEq] at this
      rw [this.1]; simp [labs]

theorem bindR_good {R : RRigid} {n : Nat} {θ : RBnd} {v : BVar} {τ : Ty} {E : Eqs} {X : List Ty}
    (hR : R v = false) (hrec : IsRec v τ) (hadm : ∀ a, v = .ty a → Adm a.cls τ) (hocc : v ∉ τ.vars)
    (hcn : cnB τ = true) (hl : ∀ e, v = .row e → ∀ σ ∈ tys E X, ∀ l ∈ lacksOf e σ, l ∉ labs (rowOf τ).1)
    (g : GoodR R n θ E X) (hv : (toRS θ).img v = vty v) (hτ : ∀ w ∈ τ.vars, (toRS θ).img w = vty w)
    (hvold : newB n v = false) (hτold : ∀ w ∈ τ.vars, newB n w = false) :
    GoodR R n (bindR v τ θ) (sE (one v τ) E) (sX (one v τ) X) ∧
    (∀ s, (s.img v = rsb s τ ∧ AbsR s θ) ↔ AbsR s (bindR v τ θ)) ∧
    (∀ s, s.img v = rsb s τ → (UniR s (sE (one v τ) E) (sX (one v τ) X) ↔ UniR s E X)) := by
  have hlk := toRS_bindR g.rrec hrec hv
  have hτv : ∀ w ∈ τ.vars, w ≠ v := fun w hw e => hocc (e ▸ hw)
  have fix' : ∀ w, (toRS θ).img w = vty w → w ≠ v → (toRS (bindR v τ θ)).img w = vty w := by
    intro w hw hwv; rw [hlk, img_rcomp, hw, rsb_vty, img_one_ne τ hwv]
  refine ⟨⟨?_, ?_, rowRec_bindR g.rrec hrec, ?_, ?_, ?_, ?_, ?_⟩, fun s => ?_, fun s hs => ?_⟩
  · intro p hp
    simp only [bindR, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hR
    · exact g.keys q hq
  · intro p hp a ha
    simp only [bindR, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hadm a ha
    · exact admR_rsb (respR_one hadm) (g.adm q hq a ha)
  · intro u w hw
    rw [hlk, img_rcomp] at hw
    rcases vars_rsb_one hw hrec with ⟨h1, h2⟩ | h1
    · exact fix' w (g.idem u w h1) h2
    · exact fix' w (hτ w h1) (hτv w h1)
  · intro σ hσ w hw
    obtain ⟨σ0, hσ0, rfl⟩ := tys_subst.mp hσ
    rcases vars_rsb_one hw hrec with ⟨h1, h2⟩ | h1
    · exact fix' w (g.stable σ0 hσ0 w h1) h2
    · exact fix' w (hτ w h1) (hτv w h1)
  · intro σ hσ w hw
    obtain ⟨σ0, hσ0, rfl⟩ := tys_subst.mp hσ
    rcases vars_rsb_one hw hrec with ⟨h1, _⟩ | h1
    · exact g.old σ0 hσ0 w h1
    · exact hτold w h1
  · intro p hp
    simp only [bindR, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨hvold, hτold⟩
    · refine ⟨(g.oldθ q hq).1, fun w hw => ?_⟩
      rcases vars_rsb_one hw hrec with ⟨h1, _⟩ | h1
      · exact (g.oldθ q hq).2 w h1
      · exact hτold w h1
  · intro σ hσ
    obtain ⟨σ0, hσ0, rfl⟩ := tys_subst.mp hσ
    exact cn_one hrec hcn (g.cn σ0 hσ0) fun e he l hle => hl e he σ0 hσ0 l hle
  · constructor
    · rintro ⟨h1, h2⟩
      have hcs := rcomp_one hrec h1
      intro u; rw [hlk, img_rcomp, rsb_rsb, hcs]; exact h2 u
    · intro h3
      have h1 : s.img v = rsb s τ := by
        have := h3 v; rw [hlk, img_rcomp, hv, rsb_vty, img_one_self hrec] at this; exact this.symm
      have hcs := rcomp_one hrec h1
      refine ⟨h1, fun u => ?_⟩
      have := h3 u; rw [hlk, img_rcomp, rsb_rsb, hcs] at this; exact this
  · exact uniR_absorb (rcomp_one hrec hs)

/-! ## A binding step for an equation at the head -/

theorem goodR_tail {R : RRigid} {n : Nat} {θ : RBnd} {l r : Ty} {E : Eqs} {X : List Ty}
    (g : GoodR R n θ ((l, r) :: E) X) : GoodR R n θ E (l :: X) := by
  have h : ∀ τ ∈ tys E (l :: X), τ ∈ tys ((l, r) :: E) X := fun τ hτ => by
    rcases tys_frame_cons.mp hτ with rfl | hτ
    · exact tys_cons.mpr (.inl rfl)
    · exact tys_cons.mpr (.inr (.inr hτ))
  exact ⟨g.keys, g.adm, g.rrec, g.idem, fun τ hτ => g.stable τ (h τ hτ), fun τ hτ => g.old τ (h τ hτ),
    g.oldθ, fun τ hτ => g.cn τ (h τ hτ)⟩

/-- The equation `vty v ≐ τ` at the head (or `τ ≐ vty v`, `swap`), bound as `v ↦ τ` with the left
    side `x` (an image of which is `s v` for every unifier) pushed on the frame. -/
theorem bindR_case {R : RRigid} {n : Nat} {θ : RBnd} {v : BVar} {τ x : Ty} {rest : Eqs} {X : List Ty}
    {cur : Eqs} (hR : R v = false) (hrec : IsRec v τ) (hadm : ∀ a, v = .ty a → Adm a.cls τ) (hocc : v ∉ τ.vars)
    (hl : ∀ e, v = .row e → ∀ σ ∈ tys rest (x :: X), ∀ l ∈ lacksOf e σ, l ∉ labs (rowOf τ).1)
    (g : GoodR R n θ cur X)
    (hcur : ∀ s, UniR s cur X ↔ s.img v = rsb s τ ∧ UniR s rest (x :: X))
    (hsub : ∀ σ ∈ tys rest (x :: X), σ ∈ tys cur X) (hτ : τ ∈ tys cur X) (hvc : vty v ∈ tys cur X) :
    GoodR R n (bindR v τ θ) (sE (one v τ) rest) (sX (one v τ) (x :: X)) ∧
      CorrR R n cur X θ (sE (one v τ) rest) (sX (one v τ) (x :: X)) (bindR v τ θ) := by
  have g1 : GoodR R n θ rest (x :: X) :=
    ⟨g.keys, g.adm, g.rrec, g.idem, fun σ hσ => g.stable σ (hsub σ hσ), fun σ hσ => g.old σ (hsub σ hσ),
     g.oldθ, fun σ hσ => g.cn σ (hsub σ hσ)⟩
  have hv : (toRS θ).img v = vty v := g.stable _ hvc v (by rw [vars_vty]; exact List.mem_singleton_self _)
  obtain ⟨g', ha, hu⟩ := bindR_good hR hrec hadm hocc (g.cn τ hτ) hl g1 hv (fun w hw => g.stable τ hτ w hw)
    (g.old _ hvc v (by rw [vars_vty]; exact List.mem_singleton_self _)) (fun w hw => g.old τ hτ w hw)
  refine ⟨g', fun s h1 h2 => ?_, fun s _ hr h1 h2 => ⟨s, fun _ _ => rfl, hr, ?_⟩⟩
  · obtain ⟨e1, e2⟩ := (ha s).mpr h2
    exact ⟨(hcur s).mpr ⟨e1, (hu s e1).mp h1⟩, e2⟩
  · obtain ⟨e1, e2⟩ := (hcur s).mp h1
    exact ⟨(hu s e1).mpr e2, (ha s).mp ⟨e1, h2⟩⟩

/-! ## A refinement (K6) -/

theorem refineR_case {R : RRigid} {n : Nat} {θ : RBnd} {b : TyVar} {m : Cls} {E : Eqs} {X : List Ty}
    (hR : R (.ty b) = false) (hm : m.le b.cls = true) (g : GoodR R n θ E X)
    (hb : (toRS θ).img (.ty b) = vty (.ty b)) (hbold : newB n (.ty b) = false)
    (hadm : ∀ s, FixR R s → RespR s → UniR s E X → Adm m (s.t b)) :
    GoodR R (n + 1) (bindR (.ty b) (.var (.fresh n m)) θ) (sE (one (.ty b) (.var (.fresh n m))) E)
        (sX (one (.ty b) (.var (.fresh n m))) X) ∧
      CorrR R n E X θ (sE (one (.ty b) (.var (.fresh n m))) E) (sX (one (.ty b) (.var (.fresh n m))) X)
        (bindR (.ty b) (.var (.fresh n m)) θ) := by
  have hγ : ∀ w, w ∈ (Ty.var (.fresh n m)).vars → w = .ty (.fresh n m) := fun w hw => by
    simpa [Ty.vars] using hw
  have hγnew : newB n (.ty (.fresh n m)) = true := isNew_fresh_self n m
  have hbγ : BVar.ty b ≠ .ty (.fresh n m) := fun e => by rw [e, hγnew] at hbold; cases hbold
  have g1 : GoodR R (n + 1) θ E X :=
    ⟨g.keys, g.adm, g.rrec, g.idem, g.stable, fun τ hτ w hw => newB_mono (Nat.le_succ n) (g.old τ hτ w hw),
     fun p hp => ⟨newB_mono (Nat.le_succ n) (g.oldθ p hp).1, fun w hw => newB_mono (Nat.le_succ n) ((g.oldθ p hp).2 w hw)⟩,
     g.cn⟩
  have hγfree : (toRS θ).img (.ty (.fresh n m)) = vty (.ty (.fresh n m)) := by
    rw [img_toRS g.rrec]
    cases hf : FMap.find? θ (.ty (.fresh n m)) with
    | none => rfl
    | some τ => have := (g.oldθ _ (rfind?_mem hf)).1; rw [hγnew] at this; cases this
  obtain ⟨g', ha, hu⟩ := bindR_good (τ := .var (.fresh n m)) (E := E) (X := X) hR trivial
    (fun a e => by cases e; exact admC_var_iff.mpr (by simpa [TyVar.cls] using hm))
    (fun h => hbγ (hγ _ h)) rfl (fun e he => by cases he) g1 hb (fun w hw => by rw [hγ w hw]; exact hγfree)
    (newB_mono (Nat.le_succ n) hbold) (fun w hw => by rw [hγ w hw]; exact isNew_fresh_succ n m)
  refine ⟨g', fun s h1 h2 => ?_, fun s hs hr h1 h2 => ?_⟩
  · obtain ⟨e1, e2⟩ := (ha s).mpr h2; exact ⟨(hu s e1).mp h1, e2⟩
  · let s' : RSub := ⟨fun c => if c = .fresh n m then s.t b else s.t c, s.r⟩
    have ag : ∀ v, newB n v = false → s'.img v = s.img v := by
      intro v hv
      cases v with
      | ty c =>
        simp only [RSub.img, s']; rw [if_neg]; rintro rfl; rw [hγnew] at hv; cases hv
      | row e => rfl
    have agT : ∀ τ : Ty, (∀ w ∈ τ.vars, newB n w = false) → rsb s' τ = rsb s τ :=
      fun τ hτ => rsb_congr τ fun w hw => ag w (hτ w hw)
    have e1 : s'.img (.ty b) = rsb s' (.var (.fresh n m)) := by
      simp [RSub.img, rsb, s']
    refine ⟨s', ag, fun c => ?_, (hu s' e1).mpr ⟨?_, ?_⟩, (ha s').mp ⟨e1, ?_⟩⟩
    · simp only [s']
      split
      · rename_i e; subst e; exact hadm s hs hr h1
      · exact hr c
    · intro e he
      rw [agT _ (fun w hw => g.old e.1 (mem_tys.mpr (.inr ⟨e, he, .inl rfl⟩)) w hw),
        agT _ (fun w hw => g.old e.2 (mem_tys.mpr (.inr ⟨e, he, .inr rfl⟩)) w hw)]
      exact h1.1 e he
    · intro τ hτ; rw [agT τ (g.old τ hτ)]; exact h1.2 τ hτ
    · intro u
      by_cases hun : newB n u = true
      · have : (toRS θ).img u = vty u := by
          rw [img_toRS g.rrec]
          cases hf : FMap.find? θ u with
          | none => rfl
          | some τ => have := (g.oldθ _ (rfind?_mem hf)).1; rw [hun] at this; cases this
        rw [this, rsb_vty]
      · have huo : newB n u = false := by simpa using hun
        have hθu : ∀ w ∈ ((toRS θ).img u).vars, newB n w = false := by
          intro w hw
          rw [img_toRS g.rrec] at hw
          cases hf : FMap.find? θ u with
          | none => rw [hf] at hw; simp only [Option.getD_none, vars_vty, List.mem_singleton] at hw; subst hw; exact huo
          | some τ => rw [hf] at hw; exact (g.oldθ _ (rfind?_mem hf)).2 w hw
        rw [agT _ hθu, ag u huo]; exact h2 u

end StandardElm.Stat.Complete
