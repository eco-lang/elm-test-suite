/-
  A Standard Definition of Elm? Mechanisation: unification over the full static type language and
  its refutation theorem, plan step 11, milestone (a) ("The mathematics", section 4).

  A constraint is an equation between terms, a field constraint `has r l u` (r is a record type
  whose row gives the label l the type u, first occurrence, as `Row.Sub` reads a row: the premise of
  r:s-atpat-record and r:s-atexp-update), or a class constraint `cls t κ` (t ∈ Adm κ). A solution is
  a valuation of the metavariables satisfying every constraint; type variables of terms are
  constants (the rigid variables of section 1, here every variable a derivation cannot choose).

  The algorithm keeps a work list and a list of *stuck* constraints (field and class constraints on
  a metavariable). A step takes the first work item:
  - an equation: identical metavariables are dropped; a metavariable against a term is bound (U2,
    fail if it occurs in the term, K3), the binding applied everywhere and the stuck constraints on
    it woken; constructors are decomposed (U3, U4, records label by label, U5 for closed rows and
    rigid tails) or fail (U6);
  - a field constraint: on a record, the field's equation, or failure if the label is missing; on a
    metavariable, a second field constraint with the same label gives an equation, a class other than
    `any` fails (records are only in Adm any), otherwise it is stuck; on anything else, failure;
  - a class constraint: `any` is dropped; a constant variable is checked (K5); a constructed type is
    decomposed by D(κ, t) (K5); a function or record type fails; on a metavariable, two classes with
    no meet fail (K4), a field constraint fails, otherwise it is stuck.

  Every step keeps every solution (the valuation is the same before and after), and a failing step
  has none: `unifyF_fail`. Termination is not needed for refutation; the loop runs on fuel.

  Deviation from the specification: no flexible row variables and no lacks sets (a row whose
  extension a derivation chooses is a metavariable with field constraints), class refinement by
  stuck class constraints instead of fresh variables, no accumulated substitution (refutation
  only); the mgu and factorisation of (b) to (d) are not attempted here.
-/
import StandardElmMech.Stat.Complete.Classes

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

inductive Con where
  | eq (a b : T)
  | has (r : T) (l : Lab) (u : T)
  | cls (a : T) (k : Cls)
  /-- A binding made by unification, kept (never processed again) so that a solved problem
      records what every solution gives its metavariables. -/
  | bound (q : Path) (s : T)
  deriving Repr, Inhabited

def Con.holds (ν : Val) : Con → Prop
  | .eq a b => a.ev ν = b.ev ν
  | .has r l u => ∃ ρ tl, r.ev ν = .record ρ tl ∧ Row.lookup ρ l = some (u.ev ν)
  | .cls a k => Adm k (a.ev ν)
  | .bound q s => ν q = s.ev ν

def Holds (ν : Val) (cs : List Con) : Prop := ∀ c ∈ cs, c.holds ν

theorem Holds.append {ν : Val} {a b : List Con} : Holds ν (a ++ b) ↔ Holds ν a ∧ Holds ν b := by
  unfold Holds; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

theorem Holds.cons {ν : Val} {c : Con} {a : List Con} : Holds ν (c :: a) ↔ c.holds ν ∧ Holds ν a := by
  unfold Holds; simp only [List.mem_cons, forall_eq_or_imp]

theorem Holds.nil {ν : Val} : Holds ν [] := fun _ h => by cases h

def Con.subst (q : Path) (s : T) : Con → Con
  | .eq a b => .eq (T.subst q s a) (T.subst q s b)
  | .has r l u => .has (T.subst q s r) l (T.subst q s u)
  | .cls a k => .cls (T.subst q s a) k
  | .bound q' s' => .bound q' (T.subst q s s')

theorem holds_subst {ν : Val} {q : Path} {s : T} (h : ν q = s.ev ν) (c : Con) :
    (c.subst q s).holds ν ↔ c.holds ν := by
  cases c <;> simp only [Con.subst, Con.holds, ev_subst h]

/-- The metavariable a stuck constraint is on. -/
def Con.head? : Con → Option Path
  | .has (.mv q) _ _ => some q
  | .cls (.mv q) _ => some q
  | _ => none

structure UState where
  work : List Con
  stuck : List Con
  deriving Repr

def UState.all (st : UState) : List Con := st.work ++ st.stuck

inductive UOutcome where
  | ok (stuck : List Con)
  | fail
  | outOfFuel
  deriving Repr, Inhabited

def UOutcome.isFail : UOutcome → Bool
  | .fail => true
  | _ => false

/-! ## Steps -/

/-- Bind q to s: apply it to every constraint, wake the stuck constraints on q, record the
    binding. -/
def bindStep (q : Path) (s : T) (rest stuck : List Con) : UState :=
  let wake := stuck.filter (fun c => c.head? == some q)
  let keep := stuck.filter (fun c => !(c.head? == some q))
  ⟨wake.map (Con.subst q s) ++ rest.map (Con.subst q s), .bound q s :: keep.map (Con.subst q s)⟩

def metaEq (q : Path) (t : T) (rest stuck : List Con) : Option UState :=
  match t with
  | .mv q' => if q' = q then some ⟨rest, stuck⟩ else some (bindStep q t rest stuck)
  | _ => if t.occ q then none else some (bindStep q t rest stuck)

/-- Pairwise equations of two argument lists; none if the lengths differ. -/
def zipEqs : List T → List T → Option (List Con)
  | [], [] => some []
  | a :: as, b :: bs => (zipEqs as bs).map (.eq a b :: ·)
  | _, _ => none

/-- Pairwise equations of two rows with the same labels in the same order; none otherwise. -/
def zipRow : List (Lab × T) → List (Lab × T) → Option (List Con)
  | [], [] => some []
  | (l, a) :: as, (l', b) :: bs => if l = l' then (zipRow as bs).map (.eq a b :: ·) else none
  | _, _ => none

/-- Equations between two terms neither of which is a metavariable (metavariables are dropped
    here; `eqStep` never passes one). -/
def rigidEq (a b : T) (rest stuck : List Con) : Option UState :=
  match a, b with
  | .mv _, _ => some ⟨rest, stuck⟩
  | _, .mv _ => some ⟨rest, stuck⟩
  | .var x, .var y => if x = y then some ⟨rest, stuck⟩ else none
  | .fn a1 b1, .fn a2 b2 => some ⟨.eq a1 a2 :: .eq b1 b2 :: rest, stuck⟩
  | .con as t, .con bs t' => if t = t' then (zipEqs as bs).map (fun es => ⟨es ++ rest, stuck⟩) else none
  | .record ρ tl, .record ρ' tl' =>
    if tl = tl' then (zipRow ρ ρ').map (fun es => ⟨es ++ rest, stuck⟩) else none
  | _, _ => none

def eqStep (a b : T) (rest stuck : List Con) : Option UState :=
  match a with
  | .mv q => metaEq q b rest stuck
  | _ =>
    match b with
    | .mv q => metaEq q a rest stuck
    | _ => rigidEq a b rest stuck

def hasSel (q : Path) (l : Lab) (c : Con) : Option T :=
  match c with
  | .has (.mv q') l' u => if q' = q ∧ l' = l then some u else none
  | _ => none

/-- A field constraint with label l on q among the stuck ones. -/
def findHas (q : Path) (l : Lab) (stuck : List Con) : Option T := stuck.findSome? (hasSel q l)

def clsSel (q : Path) (c : Con) : Bool :=
  match c with
  | .cls (.mv q') k => q' == q && k != .any
  | _ => false

/-- A class other than `any` on q among the stuck constraints. -/
def clsOn (q : Path) (stuck : List Con) : Bool := stuck.any (clsSel q)

def clashSel (q : Path) (k : Cls) (c : Con) : Bool :=
  match c with
  | .cls (.mv q') k' => q' == q && (Cls.meet k k').isNone
  | .has (.mv q') _ _ => q' == q
  | _ => false

/-- A class with no meet with k, or a field constraint, on q among the stuck constraints. -/
def clashOn (q : Path) (k : Cls) (stuck : List Con) : Bool := stuck.any (clashSel q k)

def hasStep (r : T) (l : Lab) (u : T) (rest stuck : List Con) : Option UState :=
  match r with
  | .mv q =>
    match findHas q l stuck with
    | some u' => some ⟨.eq u u' :: rest, stuck⟩
    | none => if clsOn q stuck then none else some ⟨rest, .has r l u :: stuck⟩
  | .record ρ _ =>
    match FMap.find? ρ l with
    | some x => some ⟨.eq x u :: rest, stuck⟩
    | none => none
  | _ => none

def zipCls : List T → List Cls → List Con
  | a :: as, k :: ks => .cls a k :: zipCls as ks
  | _, _ => []

def clsStep (a : T) (k : Cls) (rest stuck : List Con) : Option UState :=
  if k = .any then some ⟨rest, stuck⟩ else
  match a with
  | .mv q => if clashOn q k stuck then none else some ⟨rest, .cls a k :: stuck⟩
  | .var x => if x.cls.le k then some ⟨rest, stuck⟩ else none
  | .con as t =>
    match Cls.prop k t with
    | some ks => if as.length = ks.length then some ⟨zipCls as ks ++ rest, stuck⟩ else none
    | none => none
  | _ => none

/-- One step; `none` is failure. -/
def unifyStep (st : UState) : Option UState :=
  match st.work with
  | [] => some st
  | .eq a b :: rest => eqStep a b rest st.stuck
  | .has r l u :: rest => hasStep r l u rest st.stuck
  | .cls a k :: rest => clsStep a k rest st.stuck
  | .bound _ _ :: rest => some ⟨rest, st.stuck⟩

/-- Structural on fuel: one step per unit. -/
def unifyF : Nat → UState → UOutcome
  | 0, _ => .outOfFuel
  | n + 1, st =>
    match st.work with
    | [] => .ok st.stuck
    | _ =>
      match unifyStep st with
      | none => .fail
      | some st' => unifyF n st'

/-- Default fuel: a literal the kernel never counts down beyond the steps actually taken. -/
def unifyFuel : Nat := 2 ^ 32

def unifyCs (cs : List Con) : UOutcome := unifyF unifyFuel ⟨cs, []⟩

/-! ## Every step keeps the solutions -/

section sound
variable {ν : Val}

theorem bindStep_ok {q : Path} {s : T} (h : ν q = s.ev ν) {rest stuck : List Con}
    (hr : Holds ν rest) (hs : Holds ν stuck) : Holds ν (bindStep q s rest stuck).all := by
  unfold bindStep UState.all
  simp only
  intro c hc
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_cons] at hc
  rcases hc with (⟨c', ⟨hc', _⟩, rfl⟩ | ⟨c', hc', rfl⟩) | rfl | ⟨c', ⟨hc', _⟩, rfl⟩
  · exact (holds_subst h c').mpr (hs c' hc')
  · exact (holds_subst h c').mpr (hr c' hc')
  · exact h
  · exact (holds_subst h c').mpr (hs c' hc')

theorem metaEq_ok {q : Path} {t : T} {rest stuck : List Con} (he : ν q = t.ev ν)
    (hr : Holds ν rest) (hs : Holds ν stuck) :
    ∃ st', metaEq q t rest stuck = some st' ∧ Holds ν st'.all := by
  unfold metaEq
  split
  · rename_i q'
    split
    · exact ⟨_, rfl, Holds.append.mpr ⟨hr, hs⟩⟩
    · exact ⟨_, rfl, bindStep_ok he hr hs⟩
  · rename_i hnm
    split
    · rename_i hocc
      exact absurd he (occurs_ne ν q t hocc (fun q' e => hnm q' e))
    · exact ⟨_, rfl, bindStep_ok he hr hs⟩

theorem zipEqs_ok : ∀ (as bs : List T), T.evList ν as = T.evList ν bs →
    ∃ es, zipEqs as bs = some es ∧ Holds ν es
  | [], [], _ => ⟨[], rfl, Holds.nil⟩
  | [], _ :: _, h => by simp [T.evList] at h
  | _ :: _, [], h => by simp [T.evList] at h
  | a :: as, b :: bs, h => by
    simp only [T.evList, List.cons.injEq] at h
    obtain ⟨es, he, hh⟩ := zipEqs_ok as bs h.2
    exact ⟨.eq a b :: es, by simp [zipEqs, he], Holds.cons.mpr ⟨h.1, hh⟩⟩

theorem zipRow_ok : ∀ (as bs : List (Lab × T)), T.evRow ν as = T.evRow ν bs →
    ∃ es, zipRow as bs = some es ∧ Holds ν es
  | [], [], _ => ⟨[], rfl, Holds.nil⟩
  | [], _ :: _, h => by simp [T.evRow] at h
  | _ :: _, [], h => by simp [T.evRow] at h
  | (l, a) :: as, (l', b) :: bs, h => by
    simp only [T.evRow, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    obtain ⟨es, he, hh⟩ := zipRow_ok as bs h2
    exact ⟨.eq a b :: es, by simp [zipRow, he], Holds.cons.mpr ⟨h1, hh⟩⟩

theorem rigidEq_ok {a b : T} {rest stuck : List Con} (he : a.ev ν = b.ev ν)
    (hr : Holds ν rest) (hs : Holds ν stuck) :
    ∃ st', rigidEq a b rest stuck = some st' ∧ Holds ν st'.all := by
  have base : Holds ν (UState.all ⟨rest, stuck⟩) := Holds.append.mpr ⟨hr, hs⟩
  cases a <;> cases b <;> simp only [rigidEq] <;> simp only [T.ev] at he <;>
    (try exact ⟨_, rfl, base⟩) <;> (try cases he)
  case var.var x => exact ⟨_, by simp, base⟩
  case fn.fn a1 b1 a2 b2 =>
    simp only [Ty.fn.injEq] at he
    exact ⟨_, rfl, Holds.cons.mpr ⟨he.1, Holds.cons.mpr ⟨he.2, hr⟩⟩ |> fun h => Holds.append.mpr ⟨h, hs⟩⟩
  case con.con as t bs t' =>
    simp only [Ty.con.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    obtain ⟨es, hes, hh⟩ := zipEqs_ok as bs h1
    exact ⟨⟨es ++ rest, stuck⟩, by simp [hes], Holds.append.mpr ⟨Holds.append.mpr ⟨hh, hr⟩, hs⟩⟩
  case record.record ρ tl ρ' tl' =>
    simp only [Ty.record.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    obtain ⟨es, hes, hh⟩ := zipRow_ok ρ ρ' h1
    exact ⟨⟨es ++ rest, stuck⟩, by simp [hes], Holds.append.mpr ⟨Holds.append.mpr ⟨hh, hr⟩, hs⟩⟩

theorem eqStep_ok {a b : T} {rest stuck : List Con} (he : a.ev ν = b.ev ν)
    (hr : Holds ν rest) (hs : Holds ν stuck) :
    ∃ st', eqStep a b rest stuck = some st' ∧ Holds ν st'.all := by
  unfold eqStep
  split
  · rename_i q; exact metaEq_ok he hr hs
  · split
    · rename_i q _; exact metaEq_ok he.symm hr hs
    · exact rigidEq_ok he hr hs

theorem findHas_mem {q : Path} {l : Lab} {stuck : List Con} {u : T} (h : findHas q l stuck = some u) :
    Con.has (.mv q) l u ∈ stuck := by
  obtain ⟨c, hc, hs⟩ := List.exists_of_findSome?_eq_some h
  unfold hasSel at hs
  split at hs
  · rename_i q' l' u'
    split at hs
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hs; exact hc
    · cases hs
  · cases hs

theorem clsOn_mem {q : Path} {stuck : List Con} (h : clsOn q stuck = true) :
    ∃ k, k ≠ .any ∧ Con.cls (.mv q) k ∈ stuck := by
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp h
  unfold clsSel at hs
  split at hs
  · rename_i q' k
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact ⟨k, hk, hc⟩
  · cases hs

theorem clashOn_mem {q : Path} {k : Cls} {stuck : List Con} (h : clashOn q k stuck = true) :
    (∃ k', (Cls.meet k k').isNone = true ∧ Con.cls (.mv q) k' ∈ stuck) ∨ ∃ l u, Con.has (.mv q) l u ∈ stuck := by
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp h
  unfold clashSel at hs
  split at hs
  · rename_i q' k'
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .inl ⟨k', hk, hc⟩
  · rename_i q' l u
    simp only [beq_iff_eq] at hs
    subst hs
    exact .inr ⟨l, u, hc⟩
  · cases hs

theorem hasStep_ok {r : T} {l : Lab} {u : T} {rest stuck : List Con} (hc : (Con.has r l u).holds ν)
    (hr : Holds ν rest) (hs : Holds ν stuck) :
    ∃ st', hasStep r l u rest stuck = some st' ∧ Holds ν st'.all := by
  obtain ⟨ρ, tl, hrec, hl⟩ := hc
  unfold hasStep
  split
  · rename_i q
    split
    · rename_i u' hf
      obtain ⟨ρ', tl', hrec', hl'⟩ := hs _ (findHas_mem hf)
      simp only [T.ev] at hrec hrec'
      rw [hrec] at hrec'
      simp only [Ty.record.injEq] at hrec'
      obtain ⟨rfl, rfl⟩ := hrec'
      rw [hl] at hl'
      simp only [Option.some.injEq] at hl'
      exact ⟨_, rfl, Holds.append.mpr ⟨Holds.cons.mpr ⟨hl', hr⟩, hs⟩⟩
    · split
      · rename_i hcl
        obtain ⟨k, hk, hm⟩ := clsOn_mem hcl
        have := hs _ hm
        simp only [Con.holds, T.ev] at this hrec
        rw [hrec] at this
        exact absurd (adm_record this) hk
      · refine ⟨_, rfl, ?_⟩
        refine Holds.append.mpr ⟨hr, Holds.cons.mpr ⟨⟨ρ, tl, hrec, hl⟩, hs⟩⟩
  · rename_i ρ' tl'
    simp only [T.ev, Ty.record.injEq] at hrec
    obtain ⟨rfl, rfl⟩ := hrec
    have hf : (FMap.find? ρ' l).map (T.ev ν) = some (u.ev ν) := by
      rw [← find?_map_val]; rw [T.evRow_eq] at hl; exact hl
    cases hx : FMap.find? ρ' l with
    | none => rw [hx] at hf; cases hf
    | some x =>
      rw [hx] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      exact ⟨_, rfl, Holds.append.mpr ⟨Holds.cons.mpr ⟨hf, hr⟩, hs⟩⟩
  · rename_i hnm hnr
    exfalso
    cases r with
    | mv q => exact hnm q rfl
    | record ρ' tl' => exact hnr ρ' tl' rfl
    | var a => simp [T.ev] at hrec
    | fn a b => simp [T.ev] at hrec
    | con as t => simp [T.ev] at hrec

theorem zipCls_ok : ∀ (as : List T) (ks : List Cls), zipAdm (T.evList ν as) ks → Holds ν (zipCls as ks)
  | [], [], _ => Holds.nil
  | [], _ :: _, h => by simp [T.evList, zipAdm] at h
  | _ :: _, [], h => by simp [T.evList, zipAdm] at h
  | a :: as, k :: ks, h => by
    simp only [T.evList, zipAdm] at h
    exact Holds.cons.mpr ⟨h.1, zipCls_ok as ks h.2⟩

theorem zipAdm_length : ∀ (as : List Ty) (ks : List Cls), zipAdm as ks → as.length = ks.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zipAdm] at h
  | _ :: _, [], h => by simp [zipAdm] at h
  | _ :: as, _ :: ks, h => by simp only [zipAdm] at h; simp [zipAdm_length as ks h.2]

theorem clsStep_ok {a : T} {k : Cls} {rest stuck : List Con} (hc : (Con.cls a k).holds ν)
    (hr : Holds ν rest) (hs : Holds ν stuck) :
    ∃ st', clsStep a k rest stuck = some st' ∧ Holds ν st'.all := by
  simp only [Con.holds] at hc
  unfold clsStep
  split
  · exact ⟨_, rfl, Holds.append.mpr ⟨hr, hs⟩⟩
  · rename_i hk
    split
    · rename_i q
      split
      · rename_i hcl
        exfalso
        rcases clashOn_mem hcl with ⟨k', hm, hmem⟩ | ⟨l, u, hmem⟩
        · have h' := hs _ hmem
          simp only [Con.holds] at h'
          have := adm_meet hc h'
          rw [Option.isNone_iff_eq_none] at hm
          rw [hm] at this; cases this
        · obtain ⟨ρ, tl, hrec, _⟩ := hs _ hmem
          simp only [T.ev] at hrec hc
          rw [hrec] at hc
          exact hk (adm_record hc)
      · exact ⟨_, rfl, Holds.append.mpr ⟨hr, Holds.cons.mpr ⟨hc, hs⟩⟩⟩
    · rename_i x
      simp only [T.ev] at hc
      simp only [adm_var hc, ite_true]
      exact ⟨_, rfl, Holds.append.mpr ⟨hr, hs⟩⟩
    · rename_i as t
      simp only [T.ev] at hc
      obtain ⟨ks, hp, hz⟩ := adm_con hk hc
      rw [hp]
      have hl := zipAdm_length _ _ hz
      rw [T.evList_eq, List.length_map] at hl
      simp only [hl, ite_true]
      exact ⟨_, rfl, Holds.append.mpr ⟨Holds.append.mpr ⟨zipCls_ok as ks hz, hr⟩, hs⟩⟩
    · rename_i hnm hnv hnc
      exfalso
      cases a with
      | mv q => exact hnm q rfl
      | var x => exact hnv x rfl
      | con as t => exact hnc as t rfl
      | fn a b => exact hk (adm_fn hc)
      | record ρ tl => exact hk (adm_record hc)

theorem unifyStep_ok {st : UState} (h : Holds ν st.all) :
    ∃ st', unifyStep st = some st' ∧ Holds ν st'.all := by
  obtain ⟨work, stuck⟩ := st
  simp only [UState.all] at h
  have ⟨hw, hs⟩ := Holds.append.mp h
  match work, hw with
  | [], _ => exact ⟨_, rfl, h⟩
  | .eq a b :: rest, hw =>
    have ⟨hc, hr⟩ := Holds.cons.mp hw
    simp only [unifyStep]
    exact eqStep_ok hc hr hs
  | .has r l u :: rest, hw =>
    have ⟨hc, hr⟩ := Holds.cons.mp hw
    simp only [unifyStep]
    exact hasStep_ok hc hr hs
  | .cls a k :: rest, hw =>
    have ⟨hc, hr⟩ := Holds.cons.mp hw
    simp only [unifyStep]
    exact clsStep_ok hc hr hs
  | .bound q s :: rest, hw =>
    have ⟨_, hr⟩ := Holds.cons.mp hw
    simp only [unifyStep]
    exact ⟨_, rfl, Holds.append.mpr ⟨hr, hs⟩⟩

end sound

/-- The refutation theorem (milestone (a)): if unification fails, no valuation satisfies the
    constraints. -/
theorem unifyF_fail : ∀ (n : Nat) (st : UState), unifyF n st = .fail → ∀ ν, ¬ Holds ν st.all
  | 0, _, h, _, _ => by cases h
  | n + 1, st, h, ν, hh => by
    unfold unifyF at h
    split at h
    · cases h
    · obtain ⟨st', hs, hh'⟩ := unifyStep_ok hh
      rw [hs] at h
      exact unifyF_fail n st' h ν hh'

/-- What a solved problem records holds of every solution of the original one. -/
theorem unifyF_ok : ∀ (n : Nat) (st : UState) (stuck : List Con), unifyF n st = .ok stuck →
    ∀ ν, Holds ν st.all → Holds ν stuck
  | 0, _, _, h, _, _ => by cases h
  | n + 1, st, stuck, h, ν, hh => by
    unfold unifyF at h
    split at h
    · rename_i e
      cases h
      exact (Holds.append.mp hh).2
    · obtain ⟨st', hs, hh'⟩ := unifyStep_ok hh
      rw [hs] at h
      exact unifyF_ok n st' stuck h ν hh'

theorem unifyCs_ok {cs stuck : List Con} (h : unifyCs cs = .ok stuck) : ∀ ν, Holds ν cs → Holds ν stuck :=
  fun ν hh => unifyF_ok _ _ _ h ν (by simpa [UState.all] using hh)

/-- The binding of q a solved problem records. -/
def boundSel (q : Path) (c : Con) : Option T :=
  match c with
  | .bound q' s => if q' = q then some s else none
  | _ => none

def boundOf (q : Path) (sol : List Con) : Option T := sol.findSome? (boundSel q)

theorem boundOf_ev {ν : Val} {q : Path} {sol : List Con} {t : T} (hh : Holds ν sol) (h : boundOf q sol = some t) :
    ν q = t.ev ν := by
  obtain ⟨c, hc, hs⟩ := List.exists_of_findSome?_eq_some h
  unfold boundSel at hs
  split at hs
  · rename_i q' s
    split at hs
    · rename_i e; subst e; cases hs; exact hh _ hc
    · cases hs
  · cases hs

theorem unifyCs_fail {cs : List Con} (h : unifyCs cs = .fail) : ∀ ν, ¬ Holds ν cs := by
  intro ν hh
  exact unifyF_fail _ _ h ν (by simpa [UState.all] using hh)

end StandardElm.Stat.Complete
