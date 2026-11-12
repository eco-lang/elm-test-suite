/-
  A Standard Definition of Elm? Mechanisation: type schemes, type functions, closure and explicit
  type variables, plan step 9 (section 3). sec:static-core-types (type functions),
  sec:static-core-schemes, sec:static-core-explicit and sec:static-core-closure of static-core.tex.

  A scheme is canonical when its bound variables are `bnd 0, bnd 1, ...` in order of first
  occurrence in its body (preorder, left to right), with the vacuous ones deleted except those of
  class num, which are kept after the others. Only closure adds vacuous variables of class num
  (A93), so a scheme formed otherwise (an annotation, `typeOf`) has none: `annScheme` drops the
  vacuous explicit variables before taking the canonical form. A type function is canonical when
  its parameters are `bnd 0 .. bnd (k-1)` in order, its type parameters of class any ("the class
  of a bound type variable of a type function has no significance").
-/
import StandardElmMech.Stat.Subst

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Binding variables to types -/

/-- {τ(k)/tyrowvar(k)}: a row variable accepts only a record type; none when the lengths differ. -/
def bindSubst : List BVar → List Ty → Option Subst
  | [], [] => some Subst.id
  | .ty a :: vs, τ :: ts =>
    match bindSubst vs ts with
    | some S => some { S with ty := (a, τ) :: S.ty }
    | none => none
  | .row e :: vs, .record ρ tl :: ts =>
    match bindSubst vs ts with
    | some S => some { S with row := (e, (ρ, tl)) :: S.row }
    | none => none
  | _, _ => none

/-- σ ≻ τ (sec:static-core-schemes): τ is σ's body with its bound variables replaced by types
    (record types for row variables) for which the substitution is defined and respects classes.
    The list `ts` is the instance an annotated phrase records. -/
def Gen (σ : Scheme) (τ : Ty) : Prop :=
  ∃ ts S, bindSubst σ.bound ts = some S ∧ S.Respects ∧ S.apply σ.body = some τ

/-- σ ≻ τ at a given instance, as a Boolean. -/
def genAt (σ : Scheme) (ts : List Ty) (τ : Ty) : Bool :=
  match bindSubst σ.bound ts with
  | some S => S.respectsB && decide (S.apply σ.body = some τ)
  | none => false

theorem gen_of_genAt {σ : Scheme} {ts : List Ty} {τ : Ty} (h : genAt σ ts τ = true) : Gen σ τ := by
  unfold genAt at h
  split at h
  · rename_i S hS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ts, S, hS, (Subst.respectsB_iff S).mp h.1, h.2⟩
  · cases h

theorem genAt_of_gen {σ : Scheme} {τ : Ty} (h : Gen σ τ) : ∃ ts, genAt σ ts τ = true := by
  obtain ⟨ts, S, hS, hr, ha⟩ := h
  refine ⟨ts, ?_⟩
  simp [genAt, hS, (Subst.respectsB_iff S).mpr hr, ha]

/-- σ ≻ σ' (sec:static-core-schemes). -/
def GenS (σ σ' : Scheme) : Prop := Gen σ σ'.body ∧ ∀ v ∈ σ'.bound, v ∉ σ.tyvars

/-- θ(τ(k)): application of a type function; it need not respect classes. -/
def TyFcn.apply (θ : TyFcn) (ts : List Ty) : Option Ty :=
  match bindSubst θ.params ts with
  | some S => S.apply θ.body
  | none => none

/-! ## Canonical forms -/

/-- The variables numbered by their place: tyrowvar_i ↦ bnd i (classes kept, or class any). -/
def renumber (keepCls : Bool) : Nat → List BVar → Subst × List BVar
  | _, [] => (Subst.id, [])
  | i, .ty a :: vs =>
    let c := if keepCls then a.cls else .any
    let (S, bs) := renumber keepCls (i + 1) vs
    ({ S with ty := (a, .var (.bnd i c)) :: S.ty }, .ty (.bnd i c) :: bs)
  | i, .row e :: vs =>
    let (S, bs) := renumber keepCls (i + 1) vs
    ({ S with row := (e, ([], some (.bnd i))) :: S.row }, .row (.bnd i) :: bs)

/-- The order of a canonical scheme's bound variables: those that occur, by first occurrence, then
    the vacuous ones of class num. -/
def canonVars (bound : List BVar) (body : Ty) : List BVar :=
  let occ := dedupL (body.vars.filter fun v => decide (v ∈ bound))
  occ ++ dedupL (bound.filter fun v => v.isNumTyVar && !decide (v ∈ occ))

def Scheme.canon (σ : Scheme) : Scheme :=
  let (S, bs) := renumber true 0 (canonVars σ.bound σ.body)
  ⟨bs, (S.apply σ.body).getD σ.body⟩

def TyFcn.canon (θ : TyFcn) : TyFcn :=
  let (S, bs) := renumber false 0 (dedupL θ.params)
  ⟨bs, (S.apply θ.body).getD θ.body⟩

def natsUpTo : Nat → List Nat
  | 0 => []
  | n + 1 => natsUpTo n ++ [n]

/-- t as the type function Λα(k).α(k) t. -/
def TyName.toFcn (t : TyName) : TyFcn :=
  ⟨(natsUpTo t.arity).map (fun i => .ty (.bnd i .any)), .con ((natsUpTo t.arity).map fun i => .var (.bnd i .any)) t⟩

/-- type(scon) (sec:static-core-schemes): ∀α.α with α of class num for an integer constant. -/
def typeOf : Src.SLit → Scheme
  | .int _ => ⟨[.ty (.bnd 0 .num)], .var (.bnd 0 .num)⟩
  | .float _ _ => mono tFloatTy
  | .char _ => mono tCharTy
  | .str _ => mono tStringTy

/-! ## Closure (sec:static-core-closure) -/

/-- Clos_A σ. -/
def closScheme (A : List BVar) (σ : Scheme) : Scheme :=
  Scheme.canon ⟨σ.bound ++ diffL (dedupL σ.tyvars) A, σ.body⟩

def closVE (A : List BVar) (VE : ValEnv) : ValEnv := VE.mapV fun p => (closScheme A p.1, p.2)

/-- The closure of a group of value bindings (r:s-dec-group, r:sm-topdec-value): each scheme is
    closed also over the type variables of class num in tyvars VE \ (tyvars σ ∪ A), which are
    kept although vacuous (A93). -/
def closGroup (A : List BVar) (VE : ValEnv) : ValEnv :=
  VE.mapV fun p =>
    let extra := (diffL (dedupL (ValEnv.tyvars VE)) (p.1.tyvars ++ A)).filter BVar.isNumTyVar
    (Scheme.canon ⟨p.1.bound ++ diffL (dedupL p.1.tyvars) A ++ extra, p.1.body⟩, p.2)

/-! ## Explicit type variables (sec:static-core-explicit) -/

/-- names U: the names of the named members. -/
def namesU (U : List BVar) : List String := U.filterMap BVar.name?

/-- U is unambiguous: no name names two of its members. -/
def Unambiguous (U : List BVar) : Prop := (namesU (dedupL U)).Nodup

instance (U : List BVar) : Decidable (Unambiguous U) := by unfold Unambiguous; infer_instance

mutual
/-- tyvars ty: the type variables of the syntax occurring in a type expression. -/
def bTyNames : Src.BTy → List String
  | .tyvar a => [a]
  | .record none => []
  | .record (some row) => bTyRowNames row
  | .openRecord r row => r :: bTyRowNames row
  | .unit => []
  | .tuple t1 t2 none => bTyNames t1 ++ bTyNames t2
  | .tuple t1 t2 (some t3) => bTyNames t1 ++ bTyNames t2 ++ bTyNames t3
  | .con _ args => bTyListNames args
  | .fn t1 t2 => bTyNames t1 ++ bTyNames t2
  | .paren t => bTyNames t
def bTyRowNames : Src.BTyRow → List String
  | .field _ t none => bTyNames t
  | .field _ t (some rest) => bTyNames t ++ bTyRowNames rest
def bTyListNames : List Src.BTy → List String
  | [] => []
  | t :: ts => bTyNames t ++ bTyListNames ts
end

/-- U' is new for ty in C. -/
def NewFor (U' : List BVar) (ty : Src.BTy) (CU : List BVar) : Prop :=
  (∀ v ∈ U', v.isNamed = true) ∧
  (∀ s, s ∈ namesU U' ↔ s ∈ bTyNames ty ∧ s ∉ namesU CU) ∧
  Unambiguous (CU ++ U')

def newForB (U' : List BVar) (ty : Src.BTy) (CU : List BVar) : Bool :=
  U'.all (·.isNamed) &&
  (namesU U').all (fun s => decide (s ∈ bTyNames ty ∧ s ∉ namesU CU)) &&
  (bTyNames ty).all (fun s => decide (s ∈ namesU CU ∨ s ∈ namesU U')) &&
  decide (Unambiguous (CU ++ U'))

theorem newForB_iff (U' : List BVar) (ty : Src.BTy) (CU : List BVar) :
    newForB U' ty CU = true ↔ NewFor U' ty CU := by
  unfold newForB NewFor
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, fun s => ⟨fun hs => h2 s hs, fun ⟨ha, hb⟩ => ?_⟩, h4⟩
    rcases h3 s ha with h | h
    · exact absurd h hb
    · exact h
  · rintro ⟨h1, h2, h4⟩
    refine ⟨⟨⟨h1, fun s hs => (h2 s).mp hs⟩, fun s hs => ?_⟩, h4⟩
    by_cases hc : s ∈ namesU CU
    · exact .inl hc
    · exact .inr ((h2 s).mpr ⟨hs, hc⟩)

instance (U' : List BVar) (ty : Src.BTy) (CU : List BVar) : Decidable (NewFor U' ty CU) :=
  decidable_of_iff _ (newForB_iff U' ty CU)

/-- The scheme an annotated binding gets: ∀U'.τ, canonical (no vacuous variable: closure is the
    only source of A93's). -/
def annScheme (U' : List BVar) (τ : Ty) : Scheme :=
  Scheme.canon ⟨U'.filter (fun v => decide (v ∈ τ.vars)), τ⟩

end StandardElm.Stat
