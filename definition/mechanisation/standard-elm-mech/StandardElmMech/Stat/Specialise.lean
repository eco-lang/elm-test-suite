/-
  A Standard Definition of Elm? Mechanisation: number specialisation, plan step 10 (Lean
  definitions, "Numbers, assignments, copy names" to "The basis table").

  dynamic-core.tex, Section sec:dynamic-core-numbers: each declaration of values whose bindings
  quantify `number` variables is replaced by its default copy (every such variable Float, under its
  own names) and one copy for each other assignment of Int or Float at which the program uses it,
  under new names `x$K1$...$Kk`; each occurrence refers to the copy for its instance; a `number`
  variable nothing fixes is Float. Copies are made from the outside in. The specialisation is
  defined on step 9's annotated phrases (a principal derivation, finding B1), and its target is the
  reduced syntax of Syntax.lean, with each `let` rebuilt by Appendix A's grouping of its copies
  (`letDefs`, Choices, item 4) and each module by `Mod.Module.ofSource` (Choices, item 1).

  Everything here is structurally recursive, so that `decide +kernel` runs it.

  Group identifiers. A request names the group it asks a copy of. A top-level group is numbered by
  its place among the top-level groups of the program (modules in order); a group of a `let` by
  `T + d`, with `T` the number of top-level groups and `d` the number of `let` groups that enclose
  it. Requests on a `let` group come only from its scope, where the enclosing groups have distinct
  depths, so the number identifies the group there; it is a position, invariant under renaming.
-/
import StandardElmMech.Stat.Erase
import StandardElmMech.Derived

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (SLit BItem BExpList BImport BDatBind BTypBind BHeader)

/-! ## Numbers, assignments, copy names -/

/-- The two closed types of Adm(number) (fig:static-core-admissible). -/
inductive Num where
  | int
  | float
  deriving DecidableEq, Repr, Inhabited

def Num.key : Num → String
  | .int => "Int"
  | .float => "Float"

/-- An assignment of Int or Float to the number variables of a declaration, in their canonical
    order (Choices, item 2). -/
abbrev Assignment := List Num

def Assignment.isDefault (a : Assignment) : Bool := a.all (· == .float)
def Assignment.key (a : Assignment) : String := "$".intercalate (a.map Num.key)
def Assignment.default (k : Nat) : Assignment := List.replicate k .float

/-- Lexicographic, Float before Int. On assignments of one length this is the string order of
    their keys, which is the translator's order (Specialise.elm, `List.sortBy`). -/
def Assignment.lt : Assignment → Assignment → Bool
  | [], _ => false
  | _ :: _, [] => false
  | .float :: _, .int :: _ => true
  | .int :: _, .float :: _ => false
  | _ :: as, _ :: bs => Assignment.lt as bs

/-- The order of emission: the default copy first, then by `Assignment.lt`. -/
def Assignment.before (a b : Assignment) : Bool :=
  (a.isDefault && !b.isDefault) || (a.isDefault == b.isDefault && Assignment.lt a b)

def insertAssignment (a : Assignment) : List Assignment → List Assignment
  | [] => [a]
  | b :: bs => if a.before b then a :: b :: bs else b :: insertAssignment a bs

/-- Default first, then by `Assignment.lt`; an insertion sort by structural recursion
    (`List.mergeSort` uses well-founded recursion, which the kernel does not reduce well). -/
def orderAssignments : List Assignment → List Assignment
  | [] => []
  | a :: as => insertAssignment a (orderAssignments as)

/-- The variable a copy binds: x itself in the default copy, x$K1$...$Kk otherwise. `$` spells
    no identifier (syntax-core, identifiers), so copy names are new. -/
def copyName (x : Var) (a : Assignment) : Var :=
  if a.isDefault then x else x ++ "$" ++ a.key

/-- Every assignment of length k (2^k of them). -/
def allAssignments : Nat → List Assignment
  | 0 => [[]]
  | k + 1 => (allAssignments k).flatMap fun a => [.float :: a, .int :: a]

/-! ## The `number` variables of a group -/

mutual
/-- The type variables of a type in order of first occurrence (Choices, item 2): the arguments
    of a constructed type in order, the domain before the range, the fields of a record in label
    order (the row variable of an open record is not a type variable). Duplicates kept. -/
def Ty.tyVarsSeq : Ty → List TyVar
  | .var a => [a]
  | .record ρ _ => Ty.rowTyVarsSeq ρ
  | .fn a b => Ty.tyVarsSeq a ++ Ty.tyVarsSeq b
  | .con as _ => Ty.listTyVarsSeq as
def Ty.rowTyVarsSeq : Row → List TyVar
  | [] => []
  | (_, τ) :: rest => Ty.tyVarsSeq τ ++ Ty.rowTyVarsSeq rest
def Ty.listTyVarsSeq : List Ty → List TyVar
  | [] => []
  | τ :: rest => Ty.tyVarsSeq τ ++ Ty.listTyVarsSeq rest
end

/-- Keep the first occurrence of each element; structural on the list. -/
def dedupFirst {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedupFirst xs).filter (· ≠ x)

def BVar.tyVar? : BVar → Option TyVar
  | .ty a => some a
  | .row _ => none

/-- A member of a group as specialisation reads it: its variable, the body of its scheme in VE
    (the monotype of an unannotated member, the annotation's type of an annotated one, before
    canonical renaming), the variables of its U', and the bound variables of its scheme outside
    the group (`Clos_C VE`, sec:static-core-closure, A93) and inside it (∀U' of an annotated member,
    none of an unannotated one), each in the order of the canonical scheme's bound variables, so
    that the instance recorded at an occurrence (a list, one type per bound variable) is read
    against them. -/
structure Member where
  x : Var
  body : Ty
  uvars : List TyVar
  bOut : List BVar
  bIn : List BVar

/-- What specialisation reads at a group node of an annotated phrase. -/
structure GroupView where
  members : List Member
  /-- the variables that Clos_C VE quantifies, computed from C and VE (`closGroup`), not read from a
      stored VE', so that it is invariant under scheme equality -/
  closed : List TyVar

/-- One member, in context `A = tyvars C`, with `VEtv` the free variables of the group's VE. The
    order of the bound variables is `closGroup`'s (and `annScheme`'s): `Scheme.canon` numbers the
    variables of `canonVars`. -/
def memberOf (A VEtv : List BVar) (x : Var) (τ : Ty) (U : List BVar) (annotated : Bool) : Member :=
  let Uf := U.filter fun v => decide (v ∈ τ.vars)
  let σtv := diffL τ.tyvars Uf
  let extra := (diffL VEtv (σtv ++ A)).filter BVar.isNumTyVar
  { x := x, body := τ, uvars := U.filterMap BVar.tyVar?,
    bOut := canonVars (Uf ++ diffL (dedupL σtv) A ++ extra) τ,
    bIn := if annotated then canonVars Uf τ else [] }

/-- The variables an occurrence of a member binds outside its group: those its scheme binds, then
    every other variable of the group's declaration `V`. Outside the group nothing at the
    occurrence fixes a variable of the declaration that the member's scheme does not mention, so it
    is Float (sec:dynamic-core-numbers, "a variable that nothing at the occurrence fixes is Float";
    Choices, item 3), and never the enclosing copy's: annotation variables are named, so the same
    variable can belong to an enclosing declaration too, and reading the enclosing copy's assignment
    would make the result depend on the derivation (finding of 2026-11-12, `Stat/RenameCounterexample.lean`).
    Choices, item 5 (the enclosing copy's type) applies only to occurrences inside the group. -/
def Member.bOutAll (V : List TyVar) (m : Member) : List BVar :=
  m.bOut ++ (V.filter fun v => !(m.bOut.contains (.ty v))).map .ty

/-- The members of a value binding, in group order. -/
def AValBind.members (A VEtv : List BVar) : AValBind → List Member
  | .var x ann τ _ rest =>
    memberOf A VEtv x τ (annU ann) ann.isSome ::
      (match rest with
       | none => []
       | some vb => AValBind.members A VEtv vb)
  | .pat p _ => p.ve.map fun (x, (σ, _)) => memberOf A VEtv x σ.body [] false

/-- The view of the group `val VE vb` in a context with free variables `A`. -/
def groupView (A : List BVar) (VE : ValEnv) (vb : AValBind) : GroupView :=
  let ms := vb.members A (dedupL (ValEnv.tyvars VE))
  ⟨ms, ms.flatMap fun m => m.bOut.filterMap BVar.tyVar?⟩

/-- The number variables of the declaration (sec:dynamic-core-numbers), canonical order. -/
def GroupView.numVars (g : GroupView) : List TyVar :=
  (dedupFirst (g.members.flatMap (·.body.tyVarsSeq))).filter fun α =>
    α.cls == .num && (g.closed.contains α || g.members.any (·.uvars.contains α))

/-! ## Resolution, scopes and occurrences -/

/-- The assignments of the copies that enclose a position, innermost first. -/
abbrev NumEnv := List (TyVar × Num)

/-- A type of Adm(number) read under ρ; a number variable that ρ does not assign is Float (the
    default of sec:dynamic-core-numbers, A27). `none` for any other type, which a derivation
    never gives an integer constant or a number variable's instance. -/
def resolve (ρ : NumEnv) : Ty → Option Num
  | .con [] t => if t = tInt then some .int else if t = tFloat then some .float else none
  | .var α => if α.cls = .num then some ((ρ.lookup α).getD .float) else none
  | _ => none

/-- What an occurrence of a variable refers to: nothing to specialise (a lambda or pattern
    variable, a constructor, a basic value, a group without number variables), a group with
    number variables `V` (its identifier, the member's scheme body and the bound variables of the
    scheme seen at the occurrence), or an Elm text of the test basis in `basisCopies`. -/
inductive Ref where
  | plain
  | group (gid : Nat) (V : List TyVar) (body : Ty) (bv : List BVar)
  | basis (V : List TyVar) (body : Ty) (bv : List BVar)

def mkRef (gid : Nat) (V : List TyVar) (body : Ty) (bv : List BVar) : Ref :=
  if V.isEmpty then .plain else .group gid V body bv

/-- Local binders, innermost first; names not found here are resolved through the module's own
    top level and then through the module's provider map (`provider`). -/
structure Scope where
  locals : List (Var × Ref)
  /-- the current module's top-level groups, seen from outside each group -/
  top : List (Var × Ref)
  /-- the top-level groups of earlier modules with number variables, and the basis table -/
  global : List ((ModId × Var) × Ref)
  /-- the provider map of the module's imports (sec:static-modules-providers) -/
  prov : ProvMap

def Scope.push (Γ : Scope) (rs : List (Var × Ref)) : Scope := { Γ with locals := rs ++ Γ.locals }

/-- The variables a pattern binds, as plain local binders. -/
def Scope.pushPlain (Γ : Scope) (VE : ValEnv) : Scope := Γ.push (VE.map fun p => (p.1, .plain))

/-- The module that provides an identifier, when exactly one does. -/
def provider (π : ProvMap) (q : Option ModId) (x : Var) : Option ModId :=
  match FMap.find? π ⟨q, .val x⟩ with
  | some [m] => some m
  | _ => none

def Scope.globalRef (Γ : Scope) (q : Option ModId) (x : Var) : Ref :=
  if Γ.global.any (·.1.2 == x) then
    match provider Γ.prov q x with
    | some m => (Γ.global.lookup (m, x)).getD .plain
    | none => .plain
  else .plain

def Scope.ref (Γ : Scope) (lv : LongId) : Ref :=
  match lv.qual with
  | none =>
    match Γ.locals.lookup lv.id with
    | some r => r
    | none =>
      match Γ.top.lookup lv.id with
      | some r => r
      | none => Γ.globalRef none lv.id
  | some q => Γ.globalRef (some q) lv.id

inductive SpecError where
  | notANumber | unresolved (x : String) | recordPatternCopy (x : String)
  | missingBasisCopy (m : ModId) (x : Var) | copyFuel | portType | mainShape
  | noModule (m : ModId)
  deriving DecidableEq, Repr

/-- The number one variable `v` of the declaration takes at an occurrence (Choices, items 3 and
    5): the instance's type when the scheme seen here binds `v` and its body mentions it; Float when
    the scheme binds it and its body does not (A93); the enclosing copy's when the scheme does not
    bind it. `pairs` is the instance keyed by the scheme's bound variables. -/
def occNum (ρ : NumEnv) (bv : List BVar) (bodyVars : List TyVar) (pairs : List (BVar × Ty))
    (v : TyVar) : Except SpecError Num :=
  if bv.contains (.ty v) then
    if bodyVars.contains v then
      match (pairs.lookup (.ty v)).bind (resolve ρ) with
      | some n => .ok n
      | none => .error .notANumber
    else .ok .float
  else
    match resolve ρ (.var v) with
    | some n => .ok n
    | none => .error .notANumber

def occNums (ρ : NumEnv) (bv : List BVar) (bodyVars : List TyVar) (pairs : List (BVar × Ty)) :
    List TyVar → Except SpecError Assignment
  | [] => .ok []
  | v :: vs => do
    let n ← occNum ρ bv bodyVars pairs v
    let ns ← occNums ρ bv bodyVars pairs vs
    pure (n :: ns)

/-- The assignment an occurrence selects. -/
def occAssignment (ρ : NumEnv) (V : List TyVar) (bv : List BVar) (body : Ty) (inst : List Ty) :
    Except SpecError Assignment :=
  occNums ρ bv body.tyVarsSeq (bv.zip inst) V

/-- A copy of a group at an assignment. -/
abbrev Req := Nat × Assignment

structure Spec (α : Type) where
  out : α
  reqs : List Req

/-- An occurrence of `lv` with instance `inst`: the copy it refers to, and the request for it
    (none for a value of the basis, whose copies the basis binds). The qualifier is kept. -/
def specOcc (ρ : NumEnv) (Γ : Scope) (lv : LongId) (inst : List Ty) :
    Except SpecError (LongId × List Req) :=
  match Γ.ref lv with
  | .plain => .ok (lv, [])
  | .group gid V body bv => do
    let a ← occAssignment ρ V bv body inst
    pure (⟨lv.qual, copyName lv.id a⟩, [(gid, a)])
  | .basis V body bv => do
    let a ← occAssignment ρ V bv body inst
    pure (⟨lv.qual, copyName lv.id a⟩, [])

/-- A special constant of an expression: an integer constant at Int or at Float. -/
def specSCon (ρ : NumEnv) : SLit → Ty → Except SpecError SCon
  | .int n, τ =>
    match resolve ρ τ with
    | some .int => .ok (.int n)
    | some .float => .ok (.intF n)
    | none => .error .notANumber
  | .float m e, _ => .ok (.float m e)
  | .char c, _ => .ok (.char c)
  | .str s, _ => .ok (.str s)

/-- A special constant of a pattern: an integer constant is always at Int (r:s-atpat-scon). -/
def patSCon : SLit → SCon
  | .int n => .int n
  | .float m e => .float m e
  | .char c => .char c
  | .str s => .str s

/-! ## Patterns -/

def APatRow.firstLabel : Option APatRow → String
  | some (.field l _ _) => l
  | none => ""

mutual
/-- A pattern without its types; in the copy of a pattern binding at assignment `a`, each variable
    renamed to `copyName x a` (the default copy keeps the names). A record pattern binds the
    variables spelt as its labels and cannot be renamed (Issues, item 4). -/
def erAtPat (a : Assignment) : AAtPat → Except SpecError AtPat
  | .wild _ => .ok .wild
  | .scon sc _ => .ok (.scon (patSCon sc))
  | .var x _ => .ok (.var (copyName x a))
  | .con lc _ _ => .ok (.con lc)
  | .unit => .ok .unit
  | .tuple p1 p2 p3 => do
    let q1 ← erPat a p1
    let q2 ← erPat a p2
    let q3 ← erPatOpt a p3
    pure (.tuple q1 q2 q3)
  | .nil _ => .ok .nil
  | .record row _ =>
    if a.isDefault then .ok (.record (erPatRowOpt row))
    else .error (.recordPatternCopy (APatRow.firstLabel row))
  | .paren p => do
    let q ← erPat a p
    pure (.paren q)
def erPatRow : APatRow → PatRow
  | .field l _ rest => .field l (erPatRowOpt rest)
def erPatRowOpt : Option APatRow → Option PatRow
  | none => none
  | some r => some (erPatRow r)
def erPat (a : Assignment) : APat → Except SpecError Pat
  | .atpat p => do
    let q ← erAtPat a p
    pure (.atpat q)
  | .con lc _ args _ => do
    let qs ← erAtPatList a args
    pure (.con lc qs)
  | .cons p1 p2 => do
    let q1 ← erPat a p1
    let q2 ← erPat a p2
    pure (.cons q1 q2)
  | .as p x => do
    let q ← erPat a p
    pure (.as q (copyName x a))
def erPatOpt (a : Assignment) : Option APat → Except SpecError (Option Pat)
  | none => .ok none
  | some p => do
    let q ← erPat a p
    pure (some q)
def erAtPatList (a : Assignment) : List AAtPat → Except SpecError (List AtPat)
  | [] => .ok []
  | p :: ps => do
    let q ← erAtPat a p
    let qs ← erAtPatList a ps
    pure (q :: qs)
end

/-! ## The copy loop -/

/-- Translate each assignment of a list. -/
def translateAll (tr : Assignment → Except SpecError (Spec (List D.Def))) :
    List Assignment → Except SpecError (List (Assignment × Spec (List D.Def)))
  | [] => .ok []
  | a :: as => do
    let s ← tr a
    let rest ← translateAll tr as
    pure ((a, s) :: rest)

/-- The copies one group needs (sec:dynamic-core-numbers, "Copies are made from the outside
    in"): start from the default copy and the requests of the scope; translate each needed
    assignment once; requests of the copies on the group itself join the needed ones; the others
    are passed outwards. Each round makes at least one new copy of at most 2^k, so fuel 2^k + 1
    suffices. Structural on fuel. -/
def copyLoop (gid : Nat) (tr : Assignment → Except SpecError (Spec (List D.Def))) :
    Nat → List Assignment → List (Assignment × List D.Def) → List Req →
    Except SpecError (List (Assignment × List D.Def) × List Req)
  | 0, _, _, _ => .error .copyFuel
  | fuel + 1, pending, made, out =>
    match dedupFirst (pending.filter fun a => !(made.any (·.1 == a))) with
    | [] => .ok (made, out)
    | todo => do
      let rs ← translateAll tr todo
      let reqs := rs.flatMap (·.2.reqs)
      copyLoop gid tr fuel ((reqs.filter (·.1 == gid)).map (·.2))
        (made ++ rs.map fun (a, s) => (a, s.out)) (out ++ reqs.filter (·.1 != gid))

/-- The definitions of the copies made, in the order of emission (Choices, item 4): the default
    copy first, then the others by `Assignment.lt`; within a copy, the members in group order. -/
def emitCopies (made : List (Assignment × List D.Def)) : List D.Def :=
  (orderAssignments (made.map (·.1))).flatMap fun a => (made.lookup a).getD []

/-! ## Specialisation -/

mutual
def specAtExp (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) : AAtExp → Except SpecError (Spec AtExp)
  | .scon sc τ => do
    let c ← specSCon ρ sc τ
    pure ⟨.scon c, []⟩
  | .var lv inst _ => do
    let (lv', r) ← specOcc ρ Γ lv inst
    pure ⟨.var lv', r⟩
  | .con lc _ _ => .ok ⟨.con lc, []⟩
  | .op o _ _ => .ok ⟨.op o, []⟩
  | .unit => .ok ⟨.unit, []⟩
  | .tuple e1 e2 e3 => do
    let s1 ← specExp ρ Γ L g e1
    let s2 ← specExp ρ Γ L g e2
    let s3 ← specExpOpt ρ Γ L g e3
    pure ⟨.tuple s1.out s2.out s3.out, s1.reqs ++ s2.reqs ++ s3.reqs⟩
  | .nil _ => .ok ⟨.nil, []⟩
  | .record row => do
    let s ← specExpRowOpt ρ Γ L g row
    pure ⟨.record s.out, s.reqs⟩
  | .update x inst _ row => do
    let (lv', r) ← specOcc ρ Γ ⟨none, x⟩ inst
    let s ← specExpRow ρ Γ L g row
    pure ⟨.update lv'.id s.out, r ++ s.reqs⟩
  | .letE (.val VE vb) e => do
    let A := L.tyvars
    let gv := groupView A VE vb
    let V := gv.numVars
    let refOut := gv.members.map fun m => (m.x, mkRef g V m.body (m.bOutAll V))
    let refIn := gv.members.map fun m => (m.x, mkRef g V m.body m.bIn)
    let body ← specExp ρ (Γ.push refOut) (L.plusVE (closGroup A VE)) (g + 1) e
    let (made, out) ← copyLoop g
      (fun a => specValBind (V.zip a ++ ρ) (Γ.push refIn) (L.plusVE VE) (g + 1) a vb)
      (2 ^ V.length + 1) (Assignment.default V.length :: (body.reqs.filter (·.1 == g)).map (·.2))
      [] (body.reqs.filter (·.1 != g))
    pure ⟨D.A (D.letDefs (emitCopies made) body.out), out⟩
  | .paren e => do
    let s ← specExp ρ Γ L g e
    pure ⟨.paren s.out, s.reqs⟩
def specExpRow (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) : AExpRow → Except SpecError (Spec ExpRow)
  | .field l e rest => do
    let s ← specExp ρ Γ L g e
    let r ← specExpRowOpt ρ Γ L g rest
    pure ⟨.field l s.out r.out, s.reqs ++ r.reqs⟩
def specExpRowOpt (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) :
    Option AExpRow → Except SpecError (Spec (Option ExpRow))
  | none => .ok ⟨none, []⟩
  | some r => do
    let s ← specExpRow ρ Γ L g r
    pure ⟨some s.out, s.reqs⟩
def specExp (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) : AExp → Except SpecError (Spec Exp)
  | .atexp a => do
    let s ← specAtExp ρ Γ L g a
    pure ⟨.atexp s.out, s.reqs⟩
  | .app e a => do
    let s1 ← specExp ρ Γ L g e
    let s2 ← specAtExp ρ Γ L g a
    pure ⟨.app s1.out s2.out, s1.reqs ++ s2.reqs⟩
  | .lam p e => do
    let q ← erAtPat [] p
    let ve := p.ve
    let s ← specExp ρ (Γ.pushPlain ve) (L.plusVE ve) g e
    pure ⟨.lam q s.out, s.reqs⟩
  | .caseE e m => do
    let s1 ← specExp ρ Γ L g e
    let s2 ← specMatch ρ Γ L g m
    pure ⟨.caseE s1.out s2.out, s1.reqs ++ s2.reqs⟩
def specExpOpt (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) :
    Option AExp → Except SpecError (Spec (Option Exp))
  | none => .ok ⟨none, []⟩
  | some e => do
    let s ← specExp ρ Γ L g e
    pure ⟨some s.out, s.reqs⟩
def specMatch (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) : AMatch → Except SpecError (Spec Match)
  | .mk mr rest => do
    let s1 ← specMRule ρ Γ L g mr
    let s2 ← specMatchOpt ρ Γ L g rest
    pure ⟨.mk s1.out s2.out, s1.reqs ++ s2.reqs⟩
def specMatchOpt (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) :
    Option AMatch → Except SpecError (Spec (Option Match))
  | none => .ok ⟨none, []⟩
  | some m => do
    let s ← specMatch ρ Γ L g m
    pure ⟨some s.out, s.reqs⟩
def specMRule (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) : AMRule → Except SpecError (Spec MRule)
  | .mk p e => do
    let q ← erPat [] p
    let ve := p.ve
    let s ← specExp ρ (Γ.pushPlain ve) (L.plusVE ve) g e
    pure ⟨.mk q s.out, s.reqs⟩
/-- The copy of one group at assignment a: its members as definitions, each binding
    `copyName x a` (a pattern binding renames the variables of its pattern). `L` is the context of
    the group's bindings (C + VE). -/
def specValBind (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) (a : Assignment) :
    AValBind → Except SpecError (Spec (List D.Def))
  | .var x ann _ e rest => do
    let s ← specExp ρ Γ (L.plusU (annU ann)) g e
    let r ← specValBindOpt ρ Γ L g a rest
    pure ⟨.fn (copyName x a) [] s.out :: r.out, s.reqs ++ r.reqs⟩
  | .pat p e => do
    let q ← erAtPat a p
    let s ← specExp ρ Γ L g e
    pure ⟨[.pat q s.out], s.reqs⟩
def specValBindOpt (ρ : NumEnv) (Γ : Scope) (L : Ctx) (g : Nat) (a : Assignment) :
    Option AValBind → Except SpecError (Spec (List D.Def))
  | none => .ok ⟨[], []⟩
  | some vb => specValBind ρ Γ L g a vb
end

/-! ## The basis table -/

/-- The values of the test basis written in Elm whose schemes quantify number variables
    (Appendix D: "Of the values of the basis written in Elm, only `abs` has a type scheme that
    quantifies a variable of class number"). The core-library texts of D2 with `number` variables
    (`List.sum`, ...) join when the dynamic test basis binds their copies (core-library.md; today
    `Mod.Btest []` binds `abs$Int` only). Their variables are read from the static basis. -/
def basisCopies : List (ModId × Var) := [("Basics", "abs")]

/-- The references of the basis table, from the schemes the static basis gives them. -/
def basisRefs (B : SBasis) : List ((ModId × Var) × Ref) :=
  basisCopies.filterMap fun (m, x) =>
    match veFind B.ME m x with
    | some (σ, _) =>
      let V := σ.bound.filterMap fun v => match v with
        | .ty α => if α.cls == .num then some α else none
        | .row _ => none
      some ((m, x), Ref.basis V σ.body σ.bound)
    | none => none

/-- The variables the copies of a basis value bind, default first. -/
def basisCopyNames (B : SBasis) (m : ModId) (x : Var) : Option (List Var) :=
  if basisCopies.contains (m, x) then
    match veFind B.ME m x with
    | some (σ, _) =>
      let k := (σ.bound.filter BVar.isNumTyVar).length
      some ((orderAssignments (allAssignments k)).map (copyName x))
    | none => none
  else none

/-! ## Modules -/

/-- The top-level declarations of a module, in order. -/
inductive TopItem where
  | value (VE : ValEnv) (vb : AValBind)
  | types (db : Option BDatBind) (tbs : List BTypBind)
  | port (x : Var)

def ATopDec.items : ATopDec → List TopItem
  | .value VE vb => [.value VE vb]
  | .types _ _ db tbs => [.types db tbs]
  | .typesSplit a1 a2 => ATopDec.items a1 ++ ATopDec.items a2
  | .port x _ _ => [.port x]
  | .seq a1 a2 => ATopDec.items a1 ++ ATopDec.items a2

/-- A top-level group with its identifier, its view (in the module's context, which has no free
    type variables: the basis is closed and the earlier top-level groups are closed) and its
    number variables. -/
structure TopGroup where
  gid : Nat
  VE : ValEnv
  vb : AValBind
  view : GroupView
  V : List TyVar

def topGroupsFrom : Nat → List TopItem → List TopGroup
  | _, [] => []
  | n, .value VE vb :: rest =>
    let gv := groupView [] VE vb
    ⟨n, VE, vb, gv, gv.numVars⟩ :: topGroupsFrom (n + 1) rest
  | n, _ :: rest => topGroupsFrom n rest

def TopGroup.refsOut (G : TopGroup) : List (Var × Ref) :=
  G.view.members.map fun m => (m.x, mkRef G.gid G.V m.body (m.bOutAll G.V))

def TopGroup.refsIn (G : TopGroup) : List (Var × Ref) :=
  G.view.members.map fun m => (m.x, mkRef G.gid G.V m.body m.bIn)

/-- The empty local context: a module's context has no free type variables. -/
def Ctx.empty : Ctx := ⟨[], [], Env.empty⟩

/-- A module's top-level groups, processed last to first (Appendix A puts a group after every group
    it refers to), each by `copyLoop` with the requests of the later groups of the module and of
    the later modules. Returns the copies made of each group, in group order, and the requests for
    earlier groups. `T` is the number of top-level groups of the program. -/
def specTop (Γ : Scope) (T : Nat) : List TopGroup → List Req →
    Except SpecError (List (List (Assignment × List D.Def)) × List Req)
  | [], inc => .ok ([], inc)
  | G :: rest, inc => do
    let (ms, inc') ← specTop Γ T rest inc
    let (made, out) ← copyLoop G.gid
      (fun a => specValBind (G.V.zip a) (Γ.push G.refsIn) (Ctx.empty.plusVE G.VE) T a G.vb)
      (2 ^ G.V.length + 1) (Assignment.default G.V.length :: (inc'.filter (·.1 == G.gid)).map (·.2))
      [] (inc'.filter (·.1 != G.gid))
    pure (made :: ms, out)

/-! ## Exposing items -/

/-- sec:dynamic-modules-reduced: an exposing item naming a copied top-level variable stands for
    the items naming the variable and each new variable of its copies; `(..)` is unchanged. Used
    for a module's header (its own copies) and for an import's items (the imported module's
    copies, and the basis table's for a basis module: `import Basics exposing (abs)` exposes `abs`
    and `abs$Int`). `copies x` is `none` when `x` has no copies. -/
def expandItem (copies : Var → Option (List Var)) : BItem → List Mod.ExpItem
  | .var x => ((copies x).getD [x]).map .var
  | .op o => [.op o]
  | .ty c => [.tycon c]
  | .tyAll c => [.opened c]

def expandItems (copies : Var → Option (List Var)) : BExpList → Mod.ExpList
  | .all => .all
  | .items is => .items (is.flatMap (expandItem copies))

/-- The variables the copies of each member of a group bind, default first (the order of
    emission); only members of groups with copies other than the default. -/
def copyTable (G : TopGroup) (made : List (Assignment × List D.Def)) : List (Var × List Var) :=
  if made.length ≤ 1 then []
  else
    let as := orderAssignments (made.map (·.1))
    G.view.members.map fun m => (m.x, as.map (copyName m.x))

end StandardElm.Stat
