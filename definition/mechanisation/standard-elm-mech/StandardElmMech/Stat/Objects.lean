/-
  A Standard Definition of Elm? Mechanisation: the semantic objects of the static semantics, plan
  step 9 (section 1). Sections sec:static-core-simple to sec:static-core-projection of
  static-core.tex and sec:static-modules-objects of static-modules.tex.

  Type variables carry their class; a variable that a type variable of the syntax names is
  `named s`, any other free variable `fresh n κ`, and a bound variable of a canonical scheme or type
  function `bnd i κ`, never free in a sentence. A row is a list of fields sorted strictly by label
  (`labLt`), so that equal rows are equal lists. The type names of the initial basis that the rules
  mention (fig:static-core-builtin) have the ids of their places in fig:static-basis-tynames; the
  generated file Generated/StaticBasis.lean binds all 22 and checks these.
-/
import StandardElmMech.Src.Bare
import StandardElmMech.Stat.FMap

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Simple objects (sec:static-core-simple) -/

/-- Classes (sec:static-core-classes). -/
inductive Cls where
  | any | num | comp | app | capp
  deriving DecidableEq, Repr, Inhabited

/-- The least partial order with num ≤ comp, capp ≤ comp, capp ≤ app, κ ≤ any. -/
def Cls.le : Cls → Cls → Bool
  | _, .any => true
  | .num, .num | .comp, .comp | .app, .app | .capp, .capp => true
  | .num, .comp | .capp, .comp | .capp, .app => true
  | _, _ => false

/-- The greatest common lower bound, if any (sec:static-core-principal: num and comp give num,
    app and comp give capp, num and app none). -/
def Cls.meet : Cls → Cls → Option Cls
  | .any, k => some k
  | k, .any => some k
  | .num, .num => some .num
  | .comp, .comp => some .comp
  | .app, .app => some .app
  | .capp, .capp => some .capp
  | .num, .comp | .comp, .num => some .num
  | .capp, .comp | .comp, .capp => some .capp
  | .capp, .app | .app, .capp => some .capp
  | .app, .comp | .comp, .app => some .capp
  | _, _ => none

/-- A19: the class of the variable a type variable of the syntax names, by its beginning. -/
def classOfName (s : String) : Cls :=
  if "number".toList.isPrefixOf s.toList then .num
  else if "comparable".toList.isPrefixOf s.toList then .comp
  else if "appendable".toList.isPrefixOf s.toList then .app
  else if "compappend".toList.isPrefixOf s.toList then .capp
  else .any

inductive TyVar where
  | named (s : String)
  | fresh (n : Nat) (c : Cls)
  | bnd (i : Nat) (c : Cls)
  deriving DecidableEq, Repr, Inhabited

def TyVar.cls : TyVar → Cls
  | .named s => classOfName s
  | .fresh _ c => c
  | .bnd _ c => c

/-- Row variables have no class. `named s` exists for every `s`; the rules name it only when
    `classOfName s = .any` (A36). -/
inductive RowVar where
  | named (s : String)
  | fresh (n : Nat)
  | bnd (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- tyrowvar: a type or a row variable. -/
inductive BVar where
  | ty (a : TyVar)
  | row (e : RowVar)
  deriving DecidableEq, Repr, Inhabited

def BVar.isBnd : BVar → Bool
  | .ty (.bnd _ _) | .row (.bnd _) => true
  | _ => false

def BVar.isNamed : BVar → Bool
  | .ty (.named _) | .row (.named _) => true
  | _ => false

/-- The name of a named variable (`names U`, sec:static-core-explicit). -/
def BVar.name? : BVar → Option String
  | .ty (.named s) | .row (.named s) => some s
  | _ => none

def BVar.isNumTyVar : BVar → Bool
  | .ty a => a.cls == .num
  | .row _ => false

/-- Type names: an identity and an arity. -/
structure TyName where
  id : Nat
  arity : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## Types (fig:static-core-compound) -/

/-- A record type is `record ρ none` (closed) or `record ρ (some ε)` (open); a constructed type
    τ(k) t is `con [τ1, ..., τk] t`. -/
inductive Ty where
  | var (a : TyVar)
  | record (row : List (Lab × Ty)) (tail : Option RowVar)
  | fn (t1 t2 : Ty)
  | con (args : List Ty) (t : TyName)
  deriving Repr, Inhabited

abbrev Row := List (Lab × Ty)

mutual
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .var n, .var m =>
    if h : n = m then isTrue (by subst h; rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .record r t, .record r' t' =>
    match Ty.decEqRow r r', _root_.decEq t t' with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | .fn a b, .fn a' b' =>
    match Ty.decEq a a', Ty.decEq b b' with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | .con as t, .con bs t' =>
    match Ty.decEqList as bs, _root_.decEq t t' with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | .var _, .record _ _ | .var _, .fn _ _ | .var _, .con _ _
  | .record _ _, .var _ | .record _ _, .fn _ _ | .record _ _, .con _ _
  | .fn _ _, .var _ | .fn _ _, .record _ _ | .fn _ _, .con _ _
  | .con _ _, .var _ | .con _ _, .record _ _ | .con _ _, .fn _ _ => isFalse (by intro e; cases e)
def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
    match Ty.decEq x y, Ty.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
def Ty.decEqRow : (a b : List (Lab × Ty)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | (l, x) :: xs, (l', y) :: ys =>
    match _root_.decEq l l', Ty.decEq x y, Ty.decEqRow xs ys with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
    | isFalse h0, _, _ => isFalse (by intro e; cases e; exact h0 rfl)
    | _, isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
end

instance : DecidableEq Ty := Ty.decEq

/-- The order of labels in a row: by the codes of their characters, lexicographically. -/
def charsLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.val < b.val then true else if a = b then charsLt as bs else false

def labLt (a b : Lab) : Bool := charsLt a.toList b.toList

/-! ## The built-in type names (fig:static-core-builtin) -/

def tInt : TyName := ⟨0, 0⟩
def tFloat : TyName := ⟨1, 0⟩
def tChar : TyName := ⟨2, 0⟩
def tString : TyName := ⟨3, 0⟩
def tUnit : TyName := ⟨4, 0⟩
def tList : TyName := ⟨5, 1⟩
def tTuple2 : TyName := ⟨6, 2⟩
def tTuple3 : TyName := ⟨7, 3⟩

def tIntTy : Ty := .con [] tInt
def tFloatTy : Ty := .con [] tFloat
def tCharTy : Ty := .con [] tChar
def tStringTy : Ty := .con [] tString
def tUnitTy : Ty := .con [] tUnit
def listTy (τ : Ty) : Ty := .con [τ] tList
def tupleTy (τ1 τ2 : Ty) : Option Ty → Ty
  | none => .con [τ1, τ2] tTuple2
  | some τ3 => .con [τ1, τ2, τ3] tTuple3

/-- τ1 → ... → τn → τ. -/
def arrows : List Ty → Ty → Ty
  | [], τ => τ
  | a :: as, τ => .fn a (arrows as τ)

/-! ## Rows -/

/-- Insert a field into a sorted row, replacing a field with the same label. -/
def Row.insert (l : Lab) (τ : Ty) : Row → Row
  | [] => [(l, τ)]
  | (l', τ') :: rest =>
    if l = l' then (l, τ) :: rest
    else if labLt l l' then (l, τ) :: (l', τ') :: rest
    else (l', τ') :: Row.insert l τ rest

/-- The modification of a sorted row by a sorted row, in one pass: the fields of both, ρ' winning
    on a shared label. -/
def Row.modifyF : Nat → Row → Row → Row
  | _, [], ρ' => ρ'
  | _, ρ, [] => ρ
  | 0, ρ, ρ' => ρ' ++ ρ
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 =>
    if l1 = l2 then (l2, τ2) :: Row.modifyF f r1 r2
    else if labLt l1 l2 then (l1, τ1) :: Row.modifyF f r1 ((l2, τ2) :: r2)
    else (l2, τ2) :: Row.modifyF f ((l1, τ1) :: r1) r2

/-- ρ + ρ' (modification) of sorted rows, sorted. -/
def Row.modify (ρ ρ' : Row) : Row := Row.modifyF (ρ.length + ρ'.length) ρ ρ'

/-- The union of two sorted rows with disjoint labels, by one pass; none when a label is shared.
    On sorted rows it is ρ + ρ' (the same list as `Row.modify`). -/
def Row.mergeF : Nat → Row → Row → Option Row
  | _, [], ρ' => some ρ'
  | _, ρ, [] => some ρ
  | 0, _, _ => none
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 =>
    if l1 = l2 then none
    else if labLt l1 l2 then
      match Row.mergeF f r1 ((l2, τ2) :: r2) with
      | some r => some ((l1, τ1) :: r)
      | none => none
    else
      match Row.mergeF f ((l1, τ1) :: r1) r2 with
      | some r => some ((l2, τ2) :: r)
      | none => none

/-- ρ + ρ' when the domains are disjoint (substitution of a row variable); none otherwise. -/
def Row.merge (ρ ρ' : Row) : Option Row := Row.mergeF (ρ.length + ρ'.length) ρ ρ'

def Row.lookup (ρ : Row) (l : Lab) : Option Ty := FMap.find? ρ l

/-- ρ ⊆ ρ' as finite maps. -/
def Row.Sub (ρ ρ' : Row) : Prop := ∀ l τ, (l, τ) ∈ ρ → Row.lookup ρ' l = some τ

def Row.subB (ρ ρ' : Row) : Bool := ρ.all fun f => Row.lookup ρ' f.1 == some f.2

theorem Row.subB_iff (ρ ρ' : Row) : Row.subB ρ ρ' = true ↔ Row.Sub ρ ρ' := by
  unfold Row.subB Row.Sub
  simp only [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h l τ hm; exact h (l, τ) hm
  · intro h f hm; exact h f.1 f.2 hm

instance (ρ ρ' : Row) : Decidable (Row.Sub ρ ρ') := decidable_of_iff _ (Row.subB_iff ρ ρ')

/-- The row of a list of fields in any order, sorted (insertion). -/
def Row.ofList (fs : List (Lab × Ty)) : Row := fs.foldl (fun acc f => Row.insert f.1 f.2 acc) []

/-! ## Schemes, type functions, environments -/

inductive IdStatus where
  | c | v
  deriving DecidableEq, Repr, Inhabited

/-- A type scheme ∀tyrowvar(k).τ (sec:static-core-schemes). -/
structure Scheme where
  bound : List BVar
  body : Ty
  deriving DecidableEq, Repr, Inhabited

def mono (τ : Ty) : Scheme := ⟨[], τ⟩

/-- A type function Λtyrowvar(k).τ (sec:static-core-types). -/
structure TyFcn where
  params : List BVar
  body : Ty
  deriving DecidableEq, Repr, Inhabited

abbrev ValEnv := FMap String (Scheme × IdStatus)
abbrev TyStr := TyFcn × ValEnv
abbrev TyEnv := FMap String TyStr

/-- An interface (I, sec:static-modules-objects), and every environment in the range of a
    qualified environment: QE empty. -/
structure IEnv where
  TE : TyEnv
  VE : ValEnv
  deriving DecidableEq, Repr, Inhabited

structure Env where
  QE : FMap ModId IEnv
  TE : TyEnv
  VE : ValEnv
  deriving DecidableEq, Repr, Inhabited

/-- C = T, U, E. `T` and `U` are lists read as sets. -/
structure Ctx where
  T : List TyName
  U : List BVar
  E : Env
  deriving DecidableEq, Repr, Inhabited

abbrev ModEnv := FMap ModId IEnv

inductive Dir where
  | out | inn
  deriving DecidableEq, Repr, Inhabited

abbrev PortEnv := FMap Var (Dir × Ty)

/-- A static basis B = T, ME, PE (sec:static-modules-objects). -/
structure SBasis where
  T : List TyName
  ME : ModEnv
  PE : PortEnv
  deriving Repr, Inhabited

/-- smId and smLongId: the value and type name spaces are disjoint. -/
inductive SmId where
  | val (x : String)
  | ty (c : String)
  deriving DecidableEq, Repr, Inhabited

structure SmLongId where
  qual : Option ModId
  id : SmId
  deriving DecidableEq, Repr, Inhabited

/-- A provider map: each identifier to its non-empty set of providing modules. -/
abbrev ProvMap := FMap SmLongId (List ModId)

/-! ## Free variables and type names -/

mutual
/-- The free type and row variables of a type, in preorder, left to right, with repetitions. -/
def Ty.vars : Ty → List BVar
  | .var a => [.ty a]
  | .record ρ none => Ty.rowVars ρ
  | .record ρ (some e) => Ty.rowVars ρ ++ [.row e]
  | .fn a b => Ty.vars a ++ Ty.vars b
  | .con as _ => Ty.listVars as
def Ty.rowVars : Row → List BVar
  | [] => []
  | (_, τ) :: rest => Ty.vars τ ++ Ty.rowVars rest
def Ty.listVars : List Ty → List BVar
  | [] => []
  | τ :: rest => Ty.vars τ ++ Ty.listVars rest
end

/-- Set difference on lists. -/
def diffL {α : Type} [DecidableEq α] (l A : List α) : List α := l.filter fun x => !decide (x ∈ A)

/-- Remove repetitions, keeping first occurrences. -/
def dedupL {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedupL xs).filter (· ≠ x)

/-- tyvars τ: the free variables (bound ones of a canonical object are `bnd`, never free). -/
def Ty.tyvars (τ : Ty) : List BVar := (τ.vars.filter fun v => !v.isBnd)

def Scheme.tyvars (σ : Scheme) : List BVar := diffL σ.body.tyvars σ.bound

/-- The free variables of the values of a finite map, each key at its first occurrence (a later
    one is shadowed, sec:static-core-compound). A key is compared with the earlier keys only when
    its value has free variables, so a closed binding costs no comparison. -/
def FMap.tyvarsBy {K V : Type} [DecidableEq K] (f : V → List BVar) : List K → FMap K V → List BVar
  | _, [] => []
  | seen, (k, v) :: rest =>
    (if (f v).isEmpty || decide (k ∈ seen) then [] else f v) ++ FMap.tyvarsBy f (k :: seen) rest

def ValEnv.tyvars (VE : ValEnv) : List BVar := FMap.tyvarsBy (fun b => b.1.tyvars) [] VE

def TyFcn.tyvars (θ : TyFcn) : List BVar := diffL θ.body.tyvars θ.params

def TyEnv.tyvars (TE : TyEnv) : List BVar :=
  FMap.tyvarsBy (fun s => s.1.tyvars ++ ValEnv.tyvars s.2) [] TE

def IEnv.tyvars (I : IEnv) : List BVar := TyEnv.tyvars I.TE ++ ValEnv.tyvars I.VE

def Env.tyvars (E : Env) : List BVar :=
  FMap.tyvarsBy IEnv.tyvars [] E.QE ++ TyEnv.tyvars E.TE ++ ValEnv.tyvars E.VE

/-- tyvars C = tyvars (E of C) ∪ U of C. -/
def Ctx.tyvars (C : Ctx) : List BVar := C.E.tyvars ++ C.U

mutual
def Ty.tynames : Ty → List TyName
  | .var _ => []
  | .record ρ _ => Ty.rowTynames ρ
  | .fn a b => Ty.tynames a ++ Ty.tynames b
  | .con as t => t :: Ty.listTynames as
def Ty.rowTynames : Row → List TyName
  | [] => []
  | (_, τ) :: rest => Ty.tynames τ ++ Ty.rowTynames rest
def Ty.listTynames : List Ty → List TyName
  | [] => []
  | τ :: rest => Ty.tynames τ ++ Ty.listTynames rest
end

def ValEnv.tynames (VE : ValEnv) : List TyName := VE.flatMap fun p => p.2.1.body.tynames
def TyEnv.tynames (TE : TyEnv) : List TyName :=
  TE.flatMap fun p => p.2.1.body.tynames ++ ValEnv.tynames p.2.2
def IEnv.tynames (I : IEnv) : List TyName := TyEnv.tynames I.TE ++ ValEnv.tynames I.VE
def Env.tynames (E : Env) : List TyName :=
  (E.QE.flatMap fun p => p.2.tynames) ++ TyEnv.tynames E.TE ++ ValEnv.tynames E.VE

/-! ## Projection, injection, modification (sec:static-core-projection) -/

def Env.empty : Env := ⟨[], [], []⟩
def Env.ofVE (VE : ValEnv) : Env := ⟨[], [], VE⟩
def IEnv.empty : IEnv := ⟨[], []⟩

/-- E + E', component by component. -/
def Env.plus (E E' : Env) : Env :=
  ⟨FMap.modify E.QE E'.QE, FMap.modify E.TE E'.TE, FMap.modify E.VE E'.VE⟩

def IEnv.plus (I I' : IEnv) : IEnv := ⟨FMap.modify I.TE I'.TE, FMap.modify I.VE I'.VE⟩

/-- Set union on lists. -/
def unionL {α : Type} [DecidableEq α] (A B : List α) : List α := A ++ diffL B A

/-- C + VE. The bindings of VE come first and a lookup takes the first binding of a key, so this is
    the modification of C's value environment by VE as a finite map, without removing the
    bindings VE shadows (their free variables are not counted, `FMap.tyvarsBy`). -/
def Ctx.plusVE (C : Ctx) (VE : ValEnv) : Ctx := { C with E := { C.E with VE := VE ++ C.E.VE } }
def Ctx.plusU (C : Ctx) (U : List BVar) : Ctx := { C with U := unionL C.U U }
def Ctx.plusE (C : Ctx) (E : Env) : Ctx := { C with E := C.E.plus E }
/-- C ⊕ TE: the type environment added, T extended by its type names. -/
def Ctx.oplusTE (C : Ctx) (TE : TyEnv) : Ctx :=
  { C with T := unionL C.T (TyEnv.tynames TE), E := { C.E with TE := FMap.modify C.E.TE TE } }
/-- C ⊕ E. -/
def Ctx.oplusE (C : Ctx) (E : Env) : Ctx := { C with T := unionL C.T E.tynames, E := C.E.plus E }

def SBasis.plus (B B' : SBasis) : SBasis :=
  ⟨unionL B.T B'.T, FMap.modify B.ME B'.ME, FMap.modify B.PE B'.PE⟩

/-- C(longvar), C(longcon): through QE for a qualified identifier. -/
def Env.lookupVal (E : Env) (lv : LongId) : Option (Scheme × IdStatus) :=
  match lv.qual with
  | none => E.VE.find? lv.id
  | some m => (E.QE.find? m).bind fun I => I.VE.find? lv.id

def Env.lookupTy (E : Env) (lc : LongId) : Option TyStr :=
  match lc.qual with
  | none => E.TE.find? lc.id
  | some m => (E.QE.find? m).bind fun I => I.TE.find? lc.id

def Ctx.lookupVal (C : Ctx) (lv : LongId) : Option (Scheme × IdStatus) := C.E.lookupVal lv
def Ctx.lookupTy (C : Ctx) (lc : LongId) : Option TyStr := C.E.lookupTy lc

/-! ## Well-formedness -/

def rowSorted : List Lab → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => labLt a b && rowSorted (b :: rest)

mutual
/-- Every row strictly sorted, every constructed type with as many arguments as its arity. -/
def Ty.wf : Ty → Bool
  | .var _ => true
  | .record ρ _ => rowSorted (ρ.map (·.1)) && Ty.rowWf ρ
  | .fn a b => Ty.wf a && Ty.wf b
  | .con as t => as.length == t.arity && Ty.listWf as
def Ty.rowWf : Row → Bool
  | [] => true
  | (_, τ) :: rest => Ty.wf τ && Ty.rowWf rest
def Ty.listWf : List Ty → Bool
  | [] => true
  | τ :: rest => Ty.wf τ && Ty.listWf rest
end

end StandardElm.Stat
