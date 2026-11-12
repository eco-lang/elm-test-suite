/-
  A Standard Definition of Elm? Mechanisation: the weak constraint generator `coreGen` and the
  refutation decider `coreRefutes`, plan step 11, milestone (a) ("The mathematics", section 5).

  `coreGen B m` walks the first module's declarations in the context of its imports and emits, node
  by node, the premises of the rules of Chapter 4 as constraints (Unify.lean) over metavariables,
  one per type a derivation chooses. A metavariable is named by the path of its node in the module
  (child i of a node at path p is at i :: p; a node's own metavariables are k :: p for indices
  no child uses), so that the valuation read off a derivation is defined node by node (`rdTop`,
  below) and CoreComplete.lean proves, by induction on the annotated module, that it satisfies the
  constraints: every derivation solves `coreGen B m`. If unification fails, no derivation exists.

  What a variable stands for (`GInfo`):
  - an imported value, constructor or operator: its scheme, instantiated at each occurrence with
    one metavariable per bound type variable, with its class (exact, as every derivation uses an
    instance of that scheme); a scheme with a bound row variable counts as `weak`;
  - a lambda- or pattern-bound variable, or an unannotated member inside its group: its type (a
    metavariable of its binding node);
  - a member annotated by a type with no variables: that type, inside and outside its group;
  - a member annotated by a type with variables, a local constructor (of a custom type or a record
    alias): a *template* (`tmpl`, CoreTmpl.lean), the normalised type with a metavariable per
    variable name and per record with an extension (so repeated variables and repeated extended
    records are linked), with the classes the names require and the fields the extended records
    have. Every derivation gives such a value a canonical form of the elaborated type (`annScheme`,
    `closScheme`, after the group's closure again), so every instance is the template under some
    valuation. An occurrence names the template's metavariables by their first positions in the
    occurrence's type. Used when every choice of sorts for the annotation's names gives a type
    whose variables are named, each name of one sort, and whose extended records are sorted
    (`goodTmpl`); otherwise `shape`;
  - an unannotated member outside its group: `shape`, every instance has the shape of the
    member's type as the group's constraints solved alone give it (functions, constructed types,
    closed parts), each occurrence a copy with fresh metavariables at the other parts; when that
    type is a metavariable with classes, a template with those classes (`mvInfo`: `y = 5; y 1`);
  - anything else (a port, a scheme with a bound row variable): `weak`, a fresh unconstrained
    metavariable at each occurrence (dropping constraints keeps every derivation a solution).

  Type expressions elaborate in an abstract context (RefuseTypes.lean's `absCtx`): the names of the
  module's own types collapse to one name per arity, and the valuation collapses the names a
  derivation chooses the same way (`gN` in `hN`). A local type may have the name of an imported
  one when the body starts with its type declarations (ruling A98: the local name denotes the local
  type throughout the module; CoreComplete.lean's `InvW`).

  An annotation's type: an annotation's variables may be type or row variables in a derivation
  (r:s-ty-tyvar, r:s-ty-rowvar), so every choice of sorts for its names is elaborated (as
  RefuseTypes.lean does) and normalised by `hN`; if all choices that elaborate agree, that is the
  annotation's type, otherwise none is used.

  Deviations from the specification (section 5 and "Lean definitions"): no flexible row variables
  (records whose extension a derivation chooses are metavariables with `has` constraints); ports
  are `weak` and local type names are collapsed per arity (so two local types of one arity are not
  told apart); metavariables are named by (reversed) paths, not by a counter; the escape
  condition, A93's closure and lacks constraints are dropped (each a dropped condition: every
  derivation stays a solution).
-/
import StandardElmMech.Stat.Complete.Unify
import StandardElmMech.Stat.RefuseTypes

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BTopDec BModule)

/-! ## What the generator knows of a variable -/

inductive GInfo where
  | weak
  | mono (t : T)
  | sch (σ : Scheme)
  /-- Every instance has the shape of the term at its functions, constructed types and closed
      parts (a member of an earlier group, or an annotated member with variables). -/
  | shape (t : T)
  /-- Every instance is the template `t` under some valuation of its metavariables satisfying
      `K` (an annotated member, a local constructor): the template's metavariables are its own,
      and each occurrence names them by their first positions in `t`. -/
  | tmpl (t : T) (K : List Con)
  deriving Inhabited

structure GCtx where
  L : FMap Var GInfo
  /-- The context of the imports: the values of other modules. -/
  C0 : Ctx
  /-- The abstract type context (RefuseTypes.lean's `absCtx`): the imports' types and the
      module's own, their names collapsed. -/
  A : Ctx

def GCtx.look (Γ : GCtx) (lv : LongId) : GInfo :=
  match lv.qual with
  | none =>
    match Γ.L.find? lv.id with
    | some g => g
    | none =>
      match Γ.C0.E.VE.find? lv.id with
      | some (σ, _) => .sch σ
      | none => .weak
  | some _ =>
    match Γ.C0.lookupVal lv with
    | some (σ, _) => .sch σ
    | none => .weak

def GCtx.add (Γ : GCtx) (L : FMap Var GInfo) : GCtx := ⟨L ++ Γ.L, Γ.C0, Γ.A⟩

/-- A metavariable resolved by the bindings a solved group records. -/
def resolveIn (sol : List Con) : T → T
  | .mv q => (boundOf q sol).getD (.mv q)
  | t => t

def clsSelOf (q : Path) (c : Con) : Option Cls :=
  match c with
  | .cls (.mv q') k => if q' = q then some k else none
  | _ => none

/-- The classes a solved group requires of a metavariable. -/
def clsOf (q : Path) (sol : List Con) : List Cls := sol.filterMap (clsSelOf q)

/-- A member whose type the group's constraints leave a metavariable: every instance has the
    classes the group requires of it (a fresh metavariable with those classes). -/
def mvInfo (sol : List Con) (q : Path) : GInfo :=
  match clsOf q sol with
  | [] => .shape (.mv q)
  | ks => .tmpl (.mv [0]) (ks.map fun k => .cls (.mv [0]) k)

def closeG (sol : List Con) : GInfo → GInfo
  | .mono t =>
    match resolveIn sol t with
    | t' => if t'.closed then .mono t' else
      match t' with
      | .mv q => mvInfo sol q
      | _ => .shape t'
  | .shape t => .shape t
  | .tmpl t K => .tmpl t K
  | _ => .weak

/-- After a group: what its members stand for outside it, given the group's solved constraints. -/
def closeL (sol : List Con) (L : FMap Var GInfo) : FMap Var GInfo := L.map fun e => (e.1, closeG sol e.2)

/-- The largest group whose constraints are solved alone (unification is quadratic). -/
def groupLimit : Nat := 400

/-- The bindings of a group's constraints solved alone (nothing if they are not solved, or the
    group is large). -/
def groupSol (cs : List Con) : List Con :=
  if cs.length ≤ groupLimit then
    match unifyCs cs with
    | .ok st => st
    | _ => []
  else []

mutual
/-- A copy of a term with a fresh metavariable (named by its position under `base`) at every
    part that is neither a function type, a constructed type, a record with no extension, nor
    closed (a substitution keeps those, and the labels of such a record). -/
def sc (base : Path) : T → T
  | .fn a b => if (T.fn a b).closed then .fn a b else .fn (sc (0 :: base) a) (sc (1 :: base) b)
  | .con as tn => if (T.con as tn).closed then .con as tn else .con (scList base 0 as) tn
  | .record ρ tl =>
    if (T.record ρ tl).closed then .record ρ tl else
    match tl with
    | none => .record (scRow base 0 ρ) none
    | some _ => .mv base
  | .mv _ => .mv base
  | .var _ => .mv base
def scList (base : Path) : Nat → List T → List T
  | _, [] => []
  | i, a :: as => sc (i :: base) a :: scList base (i + 1) as
def scRow (base : Path) : Nat → List (Lab × T) → List (Lab × T)
  | _, [] => []
  | i, (l, a) :: r => (l, sc (i :: base) a) :: scRow base (i + 1) r
end


/-! ## Templates -/

def idxL {α : Type} [DecidableEq α] (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if y = x then some 0 else (idxL x ys).map (· + 1)

/-- The names of the variables of a type, sort forgotten, in order of first occurrence. -/
def tyNames (τ : Ty) : List String := dedupL (τ.vars.filterMap BVar.name?)

mutual
/-- The records with an extension of a type, outermost, in preorder. -/
def recsT : Ty → List Ty
  | .var _ => []
  | .record ρ none => recsRow ρ
  | .record ρ (some e) => [.record ρ (some e)]
  | .fn a b => recsT a ++ recsT b
  | .con as _ => recsList as
def recsRow : Row → List Ty
  | [] => []
  | (_, x) :: r => recsT x ++ recsRow r
def recsList : List Ty → List Ty
  | [] => []
  | x :: r => recsT x ++ recsList r
end

mutual
/-- The template of a (normalised) type: a name's variable is the metavariable [0, i] (i its
    index in `ns`), a record with an extension the metavariable [1, j] (j its index in `rs`). -/
def tmplT (ns : List String) (rs : List Ty) : Ty → T
  | .var a =>
    match a with
    | .named s =>
      match idxL s ns with
      | some i => .mv [0, i]
      | none => .var a
    | _ => .var a
  | .record ρ none => .record (tmplRow ns rs ρ) none
  | .record ρ (some e) =>
    match idxL (Ty.record ρ (some e)) rs with
    | some j => .mv [1, j]
    | none => .record (tmplRow ns rs ρ) (some e)
  | .fn a b => .fn (tmplT ns rs a) (tmplT ns rs b)
  | .con as t => .con (tmplList ns rs as) t
def tmplRow (ns : List String) (rs : List Ty) : Row → List (Lab × T)
  | [] => []
  | (l, x) :: r => (l, tmplT ns rs x) :: tmplRow ns rs r
def tmplList (ns : List String) (rs : List Ty) : List Ty → List T
  | [] => []
  | x :: r => tmplT ns rs x :: tmplList ns rs r
end

/-- The classes the names require of their instances. -/
def tmplCls : Nat → List String → List Con
  | _, [] => []
  | i, s :: ns =>
    if classOfName s = .any then tmplCls (i + 1) ns else .cls (.mv [0, i]) (classOfName s) :: tmplCls (i + 1) ns

/-- The fields a record with an extension (the metavariable [1, j]) has in every instance: those
    of its row whose types contain no record with an extension. -/
def tmplHasRec (ns : List String) (rs : List Ty) (j : Nat) : Ty → List Con
  | .record ρ (some _) =>
    (ρ.map (·.1)).filterMap fun l =>
      match FMap.find? ρ l with
      | some x => if (recsT x).isEmpty then some (.has (.mv [1, j]) l (tmplT ns rs x)) else none
      | none => none
  | _ => []

def tmplHasL (ns : List String) (rs : List Ty) : Nat → List Ty → List Con
  | _, [] => []
  | j, r :: rest => tmplHasRec ns rs j r ++ tmplHasL ns rs (j + 1) rest

/-- The template of a normalised type. -/
def tmplInfo (r : Ty) : GInfo :=
  .tmpl (tmplT (tyNames r) (dedupL (recsT r)) r)
    (tmplCls 0 (tyNames r) ++ tmplHasL (tyNames r) (dedupL (recsT r)) 0 (dedupL (recsT r)))

/-- A row sorted strictly by label. -/
def sortedB : Row → Bool
  | [] => true
  | (l, _) :: r => r.all (fun p => labLt l p.1) && sortedB r

mutual
/-- Every record with an extension has a sorted row. -/
def recSorted : Ty → Bool
  | .var _ => true
  | .record ρ tl => (tl.isNone || sortedB ρ) && recSortedRow ρ
  | .fn a b => recSorted a && recSorted b
  | .con as _ => recSortedList as
def recSortedRow : Row → Bool
  | [] => true
  | (_, x) :: r => recSorted x && recSortedRow r
def recSortedList : List Ty → Bool
  | [] => true
  | x :: r => recSorted x && recSortedList r
end

/-- A type whose variables are named, each name of one sort, a row variable's name of class any,
    and whose records with an extension are sorted. -/
def goodTmpl (τ : Ty) : Bool :=
  (τ.vars.all fun v =>
    match v with
    | .ty (.named s) => !(τ.vars.contains (.row (.named s)))
    | .row (.named s) => classOfName s == .any
    | _ => false) && recSorted τ

mutual
/-- The first position (reversed path) of a metavariable in a term. -/
def fpos (q : Path) (r : Path) : T → Option Path
  | .mv q' => if q' = q then some r else none
  | .var _ => none
  | .record ρ _ => fposRow q r 0 ρ
  | .fn a b => (fpos q (0 :: r) a).or (fpos q (1 :: r) b)
  | .con as _ => fposList q r 0 as
def fposRow (q : Path) (r : Path) : Nat → List (Lab × T) → Option Path
  | _, [] => none
  | i, (_, x) :: rest => (fpos q (i :: r) x).or (fposRow q r (i + 1) rest)
def fposList (q : Path) (r : Path) : Nat → List T → Option Path
  | _, [] => none
  | i, x :: rest => (fpos q (i :: r) x).or (fposList q r (i + 1) rest)
end

/-- A template's metavariable at an occurrence: the slot of its first position. -/
def slotOf (base : Path) (t0 : T) (q : Path) : Path :=
  match fpos q [] t0 with
  | some r => r ++ base
  | none => q

mutual
def reloc (base : Path) (t0 : T) : T → T
  | .mv q => .mv (slotOf base t0 q)
  | .var a => .var a
  | .record ρ tl => .record (relocRow base t0 ρ) tl
  | .fn a b => .fn (reloc base t0 a) (reloc base t0 b)
  | .con as t => .con (relocList base t0 as) t
def relocRow (base : Path) (t0 : T) : List (Lab × T) → List (Lab × T)
  | [] => []
  | (l, x) :: r => (l, reloc base t0 x) :: relocRow base t0 r
def relocList (base : Path) (t0 : T) : List T → List T
  | [] => []
  | x :: r => reloc base t0 x :: relocList base t0 r
end

mutual
/-- Every metavariable of a term occurs in the template. -/
def occIn (t0 : T) : T → Bool
  | .mv q => (fpos q [] t0).isSome
  | .var _ => true
  | .record ρ _ => occInRow t0 ρ
  | .fn a b => occIn t0 a && occIn t0 b
  | .con as _ => occInList t0 as
def occInRow (t0 : T) : List (Lab × T) → Bool
  | [] => true
  | (_, x) :: r => occIn t0 x && occInRow t0 r
def occInList (t0 : T) : List T → Bool
  | [] => true
  | x :: r => occIn t0 x && occInList t0 r
end

/-- A template's constraints at an occurrence (those whose metavariables occur in the template). -/
def relocK (base : Path) (t0 : T) (K : List Con) : List Con :=
  K.filterMap fun c =>
    match c with
    | .cls (.mv q) k => if (fpos q [] t0).isSome then some (.cls (.mv (slotOf base t0 q)) k) else none
    | .has (.mv q) l u =>
      if (fpos q [] t0).isSome && occIn t0 u then some (.has (.mv (slotOf base t0 q)) l (reloc base t0 u)) else none
    | _ => none

/-! ## Occurrences -/

def idxTy (a : TyVar) : List BVar → Option Nat
  | [] => none
  | v :: vs => if v = .ty a then some 0 else (idxTy a vs).map (· + 1)

mutual
/-- A scheme's body with its bound type variables replaced by the occurrence's metavariables. -/
def instT (p : Path) (bs : List BVar) : Ty → T
  | .var a =>
    match idxTy a bs with
    | some i => .mv ((i + 1) :: p)
    | none => .var a
  | .record ρ tl => mkRec (instRow p bs ρ) tl
  | .fn a b => .fn (instT p bs a) (instT p bs b)
  | .con as t => .con (instList p bs as) (gN t)
def instRow (p : Path) (bs : List BVar) : Row → List (Lab × T)
  | [] => []
  | (l, x) :: r => (l, instT p bs x) :: instRow p bs r
def instList (p : Path) (bs : List BVar) : List Ty → List T
  | [] => []
  | x :: r => instT p bs x :: instList p bs r
end

/-- The classes of the instance's metavariables. -/
def instCls (p : Path) : Nat → List BVar → List Con
  | _, [] => []
  | i, .ty a :: vs => .cls (.mv ((i + 1) :: p)) a.cls :: instCls p (i + 1) vs
  | i, .row _ :: vs => instCls p (i + 1) vs

def hasRowBound (σ : Scheme) : Bool :=
  σ.bound.any fun v => match v with
    | .row _ => true
    | .ty _ => false

def schT (p : Path) (σ : Scheme) : T × List Con :=
  if hasRowBound σ then (.mv (0 :: p), []) else (instT p σ.bound σ.body, instCls p 0 σ.bound)

def occT (Γ : GCtx) (lv : LongId) (p : Path) : T × List Con :=
  match Γ.look lv with
  | .weak => (.mv (0 :: p), [])
  | .mono t => (t, [])
  | .sch σ => schT p σ
  | .shape t => (sc (0 :: 0 :: p) t, [])
  | .tmpl t K => (reloc (0 :: 0 :: p) t t, relocK (0 :: 0 :: p) t K)

def litT (sc : SLit) (p : Path) : T × List Con :=
  match sc with
  | .int _ => (.mv (0 :: p), [.cls (.mv (0 :: p)) .num])
  | .float _ _ => (ofTy tFloatTy, [])
  | .char _ => (ofTy tCharTy, [])
  | .str _ => (ofTy tStringTy, [])

def patLitT (sc : SLit) : T :=
  match sc with
  | .int _ => ofTy tIntTy
  | .float _ _ => ofTy tFloatTy
  | .char _ => ofTy tCharTy
  | .str _ => ofTy tStringTy

def tupleT (t1 t2 : T) : Option T → T
  | none => .con [t1, t2] tTuple2
  | some t3 => .con [t1, t2, t3] tTuple3

def arrowsT : List T → T → T
  | [], t => t
  | a :: as, t => .fn a (arrowsT as t)

/-! ## Annotations -/

/-- The type of an annotation, if every choice of sorts for its names that elaborates gives the same
    normalised type. -/
def annR (C0 : Ctx) (ty : BTy) : Option Ty :=
  match (RTypes.annCands ty).filterMap (fun U => (elabTy { C0 with U := U } ty).map hN) with
  | [] => none
  | r :: rest => if rest.all (· == r) then some r else none

def annT (C0 : Ctx) (ty : BTy) : Option T := (annR C0 ty).map ofTy

/-- Every choice of sorts that elaborates gives a type a template describes. -/
def annGood (C0 : Ctx) (ty : BTy) : Bool :=
  (RTypes.annCands ty).all fun U =>
    match elabTy { C0 with U := U } ty with
    | some τ => goodTmpl τ
    | none => true

def memberInfo (C0 : Ctx) (p : Path) : Option BTy → GInfo
  | none => .mono (.mv (0 :: p))
  | some ty =>
    match annR C0 ty with
    | some r => if (ofTy r).closed then .mono (ofTy r) else if annGood C0 ty then tmplInfo r else .shape (ofTy r)
    | none => .weak

def annCs (C0 : Ctx) (p : Path) : Option BTy → List Con
  | none => []
  | some ty =>
    match annT C0 ty with
    | some t => [.eq (.mv (0 :: p)) t]
    | none => []

/-! ## Patterns: the variables they bind -/

mutual
def penvAt (p : Path) : BAtPat → FMap Var GInfo
  | .var x => [(x, .mono (.mv (0 :: p)))]
  | .tuple p1 p2 p3 => FMap.modify (FMap.modify (penv (0 :: p) p1) (penv (1 :: p) p2)) (penvOpt (2 :: p) p3)
  | .record row => penvRowOpt (1 :: p) row
  | .paren q => penv (0 :: p) q
  | .wild | .scon _ | .con _ | .unit | .nil => []
def penvRow (p : Path) : BPatRow → FMap Var GInfo
  | .field l rest => FMap.modify [(l, .mono (.mv (0 :: p)))] (penvRowOpt (1 :: p) rest)
def penvRowOpt (p : Path) : Option BPatRow → FMap Var GInfo
  | none => []
  | some r => penvRow p r
def penv (p : Path) : BPat → FMap Var GInfo
  | .atpat a => penvAt (0 :: p) a
  | .con _ args => FMap.plusAll (penvList (2 :: p) args)
  | .cons p1 p2 => FMap.modify (penv (0 :: p) p1) (penv (1 :: p) p2)
  | .as q x => FMap.modify (penv (0 :: p) q) [(x, .mono (.mv (1 :: p)))]
def penvOpt (p : Path) : Option BPat → FMap Var GInfo
  | none => []
  | some q => penv p q
def penvList (p : Path) : List BAtPat → List (FMap Var GInfo)
  | [] => []
  | a :: as => penvAt (0 :: p) a :: penvList (1 :: p) as
end

mutual
/-- The row of a record pattern: one metavariable per field. -/
def prow (p : Path) : BPatRow → List (Lab × T)
  | .field l rest => rmod [(l, .mv (0 :: p))] (prowOpt (1 :: p) rest)
def prowOpt (p : Path) : Option BPatRow → List (Lab × T)
  | none => []
  | some r => prow p r
end

/-! ## Patterns: constraints -/

mutual
def gAtPat (Γ : GCtx) (p : Path) : BAtPat → T × List Con
  | .wild => (.mv (0 :: p), [])
  | .scon sc => (patLitT sc, [])
  | .var _ => (.mv (0 :: p), [])
  | .con lc => occT Γ lc p
  | .unit => (ofTy tUnitTy, [])
  | .tuple p1 p2 p3 =>
    match gPat Γ (0 :: p) p1, gPat Γ (1 :: p) p2, gPatOpt Γ (2 :: p) p3 with
    | (t1, c1), (t2, c2), (t3, c3) => (tupleT t1 t2 t3, c1 ++ c2 ++ c3)
  | .nil => (.con [.mv (0 :: p)] tList, [])
  | .record row => (.mv (0 :: p), (prowOpt (1 :: p) row).map fun f => .has (.mv (0 :: p)) f.1 f.2)
  | .paren q => gPat Γ (0 :: p) q
def gPat (Γ : GCtx) (p : Path) : BPat → T × List Con
  | .atpat a => gAtPat Γ (0 :: p) a
  | .con lc args =>
    match occT Γ lc (0 :: p), gAtPatList Γ (2 :: p) args with
    | (tc, c0), (ts, c1) => (.mv (1 :: p), c0 ++ c1 ++ [.eq tc (arrowsT ts (.mv (1 :: p)))])
  | .cons p1 p2 =>
    match gPat Γ (0 :: p) p1, gPat Γ (1 :: p) p2 with
    | (t1, c1), (t2, c2) => (.con [t1] tList, c1 ++ c2 ++ [.eq t2 (.con [t1] tList)])
  | .as q _ =>
    match gPat Γ (0 :: p) q with
    | (t, c) => (t, c ++ [.eq (.mv (1 :: p)) t])
def gPatOpt (Γ : GCtx) (p : Path) : Option BPat → Option T × List Con
  | none => (none, [])
  | some q =>
    match gPat Γ p q with
    | (t, c) => (some t, c)
def gAtPatList (Γ : GCtx) (p : Path) : List BAtPat → List T × List Con
  | [] => ([], [])
  | a :: as =>
    match gAtPat Γ (0 :: p) a, gAtPatList Γ (1 :: p) as with
    | (t, c), (ts, cs) => (t :: ts, c ++ cs)
end

/-! ## Groups: what their members stand for -/

mutual
def gVBEnv (C0 : Ctx) (p : Path) : BValBind → FMap Var GInfo
  | .var x ann _ rest => FMap.modify [(x, memberInfo C0 p ann)] (gVBEnvOpt C0 (2 :: p) rest)
  | .pat q _ => penvAt (0 :: p) q
def gVBEnvOpt (C0 : Ctx) (p : Path) : Option BValBind → FMap Var GInfo
  | none => []
  | some vb => gVBEnv C0 p vb
end

/-! ## Expressions and declarations: constraints -/

mutual
def gAtExp (Γ : GCtx) (p : Path) : BAtExp → T × List Con
  | .scon sc => litT sc p
  | .var lv => occT Γ lv p
  | .con lc => occT Γ lc p
  | .op o =>
    match OTstat o with
    | some (σ, _) => schT p σ
    | none => (.mv (0 :: p), [])
  | .unit => (ofTy tUnitTy, [])
  | .tuple e1 e2 e3 =>
    match gExp Γ (0 :: p) e1, gExp Γ (1 :: p) e2, gExpOpt Γ (2 :: p) e3 with
    | (t1, c1), (t2, c2), (t3, c3) => (tupleT t1 t2 t3, c1 ++ c2 ++ c3)
  | .nil => (.con [.mv (0 :: p)] tList, [])
  | .record row =>
    match gExpRowOpt Γ (0 :: p) row with
    | (r, c) => (.record r none, c)
  | .update x row =>
    match occT Γ ⟨none, x⟩ (0 :: p), gExpRow Γ (1 :: p) row with
    | (tx, c0), (r, c1) => (tx, c0 ++ c1 ++ r.map fun f => .has tx f.1 f.2)
  | .letE d e =>
    match gDec Γ (0 :: p) d with
    | (L, c0) =>
      match gExp (Γ.add L) (1 :: p) e with
      | (t, c1) => (t, c0 ++ c1)
  | .paren e => gExp Γ (0 :: p) e
def gExpRow (Γ : GCtx) (p : Path) : BExpRow → List (Lab × T) × List Con
  | .field l e rest =>
    match gExp Γ (0 :: p) e, gExpRowOpt Γ (1 :: p) rest with
    | (t, c), (r, c') => (rmod [(l, t)] r, c ++ c')
def gExpRowOpt (Γ : GCtx) (p : Path) : Option BExpRow → List (Lab × T) × List Con
  | none => ([], [])
  | some r => gExpRow Γ p r
def gExp (Γ : GCtx) (p : Path) : BExp → T × List Con
  | .atexp a => gAtExp Γ (0 :: p) a
  | .app e a =>
    match gExp Γ (0 :: p) e, gAtExp Γ (1 :: p) a with
    | (te, c1), (ta, c2) => (.mv (2 :: p), c1 ++ c2 ++ [.eq te (.fn ta (.mv (2 :: p)))])
  | .lam q e =>
    match gAtPat Γ (0 :: p) q, gExp (Γ.add (penvAt (0 :: p) q)) (1 :: p) e with
    | (tq, c1), (te, c2) => (.fn tq te, c1 ++ c2)
  | .caseE e m =>
    match gExp Γ (0 :: p) e, gMatch Γ (1 :: p) m with
    | (te, c1), (tm, c2) => (.mv (2 :: p), c1 ++ c2 ++ [.eq tm (.fn te (.mv (2 :: p)))])
def gExpOpt (Γ : GCtx) (p : Path) : Option BExp → Option T × List Con
  | none => (none, [])
  | some e =>
    match gExp Γ p e with
    | (t, c) => (some t, c)
def gMatch (Γ : GCtx) (p : Path) : BMatch → T × List Con
  | .mk mr rest =>
    match gMRule Γ (0 :: p) mr, gMatchOpt Γ (1 :: p) rest with
    | (t, c), (none, c') => (t, c ++ c')
    | (t, c), (some t', c') => (t, c ++ c' ++ [.eq t' t])
def gMatchOpt (Γ : GCtx) (p : Path) : Option BMatch → Option T × List Con
  | none => (none, [])
  | some m =>
    match gMatch Γ p m with
    | (t, c) => (some t, c)
def gMRule (Γ : GCtx) (p : Path) : BMRule → T × List Con
  | .mk q e =>
    match gPat Γ (0 :: p) q, gExp (Γ.add (penv (0 :: p) q)) (1 :: p) e with
    | (tq, c1), (te, c2) => (.fn tq te, c1 ++ c2)
def gDec (Γ : GCtx) (p : Path) : BDec → FMap Var GInfo × List Con
  | .val vb =>
    match gVBEnv Γ.A (0 :: p) vb with
    | Lg =>
      match gValBind (Γ.add Lg) (0 :: p) vb with
      | cs => (closeL (groupSol cs) Lg, cs)
def gValBind (Γ : GCtx) (p : Path) : BValBind → List Con
  | .var _ ann e rest =>
    match gExp Γ (1 :: p) e with
    | (te, c) => c ++ [.eq te (.mv (0 :: p))] ++ annCs Γ.A p ann ++ gValBindOpt Γ (2 :: p) rest
  | .pat q e =>
    match gAtPat Γ (0 :: p) q, gExp Γ (1 :: p) e with
    | (tq, c1), (te, c2) => c1 ++ c2 ++ [.eq te tq]
def gValBindOpt (Γ : GCtx) (p : Path) : Option BValBind → List Con
  | none => []
  | some vb => gValBind Γ p vb
end

/-! ## Modules -/

/-- What a local constructor stands for: the template of its type, when it has one. -/
def conInfo (body : Ty) : GInfo := if goodTmpl body then tmplInfo (hN body) else .weak

def gConBind (A : Ctx) (τr : Option Ty) : Src.BConBind → FMap Var GInfo
  | [] => []
  | (k, tys) :: rest =>
    FMap.modify [(k, match τr, elabTyList A tys with
      | some τ, some τs => conInfo (arrows τs τ)
      | _, _ => .weak)] (gConBind A τr rest)

/-- The constructors of custom types, as `elabDatBind` binds them, the type names collapsed. -/
def gDat (A : Ctx) : Src.BDatBind → FMap Var GInfo
  | [] => []
  | (_, ps, cb) :: rest =>
    FMap.modify
      (gConBind (A.plusU (seqVars ps (conBindExtNames cb)))
        ((elabTyList (A.plusU (seqVars ps (conBindExtNames cb))) (ps.map .tyvar)).map
          fun τs => .con τs ⟨RTypes.Did, ps.length⟩) cb)
      (gDat A rest)

/-- The constructor a record alias binds, as `elabTypBind` binds it. -/
def aliasL (A : Ctx) (tb : Src.BTypBind) : FMap Var GInfo :=
  match smlabs tb.t with
  | none => []
  | some ls =>
    [(tb.c, match elabTy (A.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
      | some (.record ρ none) =>
        match Row.lookupAll ρ ls with
        | some τs => if ρ.length = ls.length then conInfo (arrows τs (.record ρ none)) else .weak
        | none => .weak
      | _ => .weak)]

/-- The values a type declaration binds: constructors and record aliases by their templates. -/
def gTypes (A : Ctx) (db : Option Src.BDatBind) (tbs : List Src.BTypBind) : FMap Var GInfo :=
  match db with
  | none => FMap.plusAll (tbs.map (aliasL A))
  | some d => FMap.modify (gDat A d) (FMap.plusAll (tbs.map (aliasL A)))

def gTop (Γ : GCtx) (p : Path) : BTopDec → Option (FMap Var GInfo × List Con)
  | .value vb =>
    match gVBEnv Γ.A (0 :: p) vb with
    | Lg =>
      match gValBind (Γ.add Lg) (0 :: p) vb with
      | cs => some (closeL (groupSol cs) Lg, cs)
  | .seq d1 d2 =>
    match gTop Γ (0 :: p) d1 with
    | some (L1, c1) =>
      match gTop (Γ.add L1) (1 :: p) d2 with
      | some (L2, c2) => some (L2 ++ L1, c1 ++ c2)
      | none => none
    | none => none
  | .types db tbs => some (gTypes Γ.A db tbs, [])
  | .port x _ => some ([(x, .weak)], [])

/-- The abstract type context of a module (RefuseTypes.lean). -/
def absOf (B : SBasis) (C0 : Ctx) (d : BTopDec) : Ctx :=
  RTypes.absCtx (RTypes.fcol B.T) C0 (RTypes.localTE (RTypes.fcol B.T) C0 (some d))

/-- The body starts with its type declarations. -/
def startsTypes : BTopDec → Bool
  | .types _ _ => true
  | .seq (.types _ _) _ => true
  | _ => false

/-- What the simulation of type expressions needs of the basis and the module's type
    declarations (RefuseTypes.lean's `preserves`): a local type may have the name of an imported
    one when the body starts with the type declarations (ruling A98: the local name denotes the
    local type throughout the module). -/
def typesOK (B : SBasis) (C0 : Ctx) (d : BTopDec) : Bool :=
  RTypes.fixedNames.all (· ∈ B.T) && T0.all (· ∈ B.T) &&
    (RTypes.unboundB C0 (RTypes.localTE (RTypes.fcol B.T) C0 (some d)) || startsTypes d) &&
    RTypes.preserves (absOf B C0 d) d

/-- The weak constraint generator for a module in a basis: none when its imports fail, it has no
    body, or its type declarations are not simulated (`typesOK`). -/
def coreGen (B : SBasis) (m : BModule) : Option (List Con) :=
  match importCtx B m.imports, m.body with
  | some C0, some d =>
    if typesOK B C0 d then (gTop ⟨[], C0, absOf B C0 d⟩ [] d).map (·.2) else none
  | _, _ => none

/-- The largest problem `coreRefutes` attempts (unification substitutes eagerly, quadratic in the
    number of constraints; every test program of class `inference` is far below it). -/
def coreLimit : Nat := 5000

/-- Refutation by a core: unification of the first module's constraints fails. -/
def coreRefutes (B : SBasis) (sp : Src.SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | m :: _ =>
    match coreGen B m with
    | some cs => decide (cs.length ≤ coreLimit) && (unifyCs cs).isFail
    | none => false
  | [] => false

/-! ## The valuation read off a derivation -/

def elemTy : Ty → Ty
  | .con [x] _ => x
  | _ => default

def tyChild : Ty → Nat → Ty
  | .fn a _, 0 => a
  | .fn _ b, 1 => b
  | .con as _, i => as.getD i default
  | .record ρ _, i => (ρ.getD i default).2
  | _, _ => default

/-- The part of a type at a position (through functions and constructed types). -/
def subAt (τ : Ty) : Path → Ty
  | [] => τ
  | i :: q => subAt (tyChild τ i) q

/-- An occurrence's slots: [0] its type, [i+1] its instance's i-th type, 0 :: 0 :: q its type's
    part at q. -/
def rdOcc (inst : List Ty) (τ : Ty) : Path → Ty
  | [0] => hN τ
  | [i + 1] => hN (inst.getD i default)
  | 0 :: 0 :: q => subAt (hN τ) q
  | _ => default

mutual
def rdAtPat : AAtPat → Path → Ty
  | .wild τ, [0] => hN τ
  | .var _ τ, [0] => hN τ
  | .con _ inst τ, q => rdOcc inst τ q
  | .tuple p1 _ _, 0 :: q => rdPat p1 q
  | .tuple _ p2 _, 1 :: q => rdPat p2 q
  | .tuple _ _ p3, 2 :: q => rdPatOpt p3 q
  | .nil τ, [0] => hN (elemTy τ)
  | .record _ τ, [0] => hN τ
  | .record row _, 1 :: q => rdPatRowOpt row q
  | .paren p, 0 :: q => rdPat p q
  | _, _ => default
def rdPatRow : APatRow → Path → Ty
  | .field _ τ _, [0] => hN τ
  | .field _ _ rest, 1 :: q => rdPatRowOpt rest q
  | _, _ => default
def rdPatRowOpt : Option APatRow → Path → Ty
  | none, _ => default
  | some r, q => rdPatRow r q
def rdPat : APat → Path → Ty
  | .atpat a, 0 :: q => rdAtPat a q
  | .con _ inst args τ, 0 :: q => rdOcc inst (arrows (AAtPat.tyList args) τ) q
  | .con _ _ _ τ, [1] => hN τ
  | .con _ _ args _, 2 :: q => rdAtPatList args q
  | .cons p1 _, 0 :: q => rdPat p1 q
  | .cons _ p2, 1 :: q => rdPat p2 q
  | .as p _, 0 :: q => rdPat p q
  | .as p _, [1] => hN (APat.ty p)
  | _, _ => default
def rdPatOpt : Option APat → Path → Ty
  | none, _ => default
  | some p, q => rdPat p q
def rdAtPatList : List AAtPat → Path → Ty
  | a :: _, 0 :: q => rdAtPat a q
  | _ :: as, 1 :: q => rdAtPatList as q
  | _, _ => default
end

mutual
def rdAtExp : AAtExp → Path → Ty
  | .scon _ τ, [0] => hN τ
  | .var _ inst τ, q => rdOcc inst τ q
  | .con _ inst τ, q => rdOcc inst τ q
  | .op _ inst τ, q => rdOcc inst τ q
  | .tuple e1 _ _, 0 :: q => rdExp e1 q
  | .tuple _ e2 _, 1 :: q => rdExp e2 q
  | .tuple _ _ e3, 2 :: q => rdExpOpt e3 q
  | .nil τ, [0] => hN (elemTy τ)
  | .record row, 0 :: q => rdExpRowOpt row q
  | .update _ inst τ _, 0 :: q => rdOcc inst τ q
  | .update _ _ _ row, 1 :: q => rdExpRow row q
  | .letE d _, 0 :: q => rdDec d q
  | .letE _ e, 1 :: q => rdExp e q
  | .paren e, 0 :: q => rdExp e q
  | _, _ => default
def rdExpRow : AExpRow → Path → Ty
  | .field _ e _, 0 :: q => rdExp e q
  | .field _ _ rest, 1 :: q => rdExpRowOpt rest q
  | _, _ => default
def rdExpRowOpt : Option AExpRow → Path → Ty
  | none, _ => default
  | some r, q => rdExpRow r q
def rdExp : AExp → Path → Ty
  | .atexp a, 0 :: q => rdAtExp a q
  | .app e _, 0 :: q => rdExp e q
  | .app _ a, 1 :: q => rdAtExp a q
  | .app e _, [2] => hN (AExp.ty e).cod
  | .lam p _, 0 :: q => rdAtPat p q
  | .lam _ e, 1 :: q => rdExp e q
  | .caseE e _, 0 :: q => rdExp e q
  | .caseE _ m, 1 :: q => rdMatch m q
  | .caseE _ m, [2] => hN (AMatch.ty m).cod
  | _, _ => default
def rdExpOpt : Option AExp → Path → Ty
  | none, _ => default
  | some e, q => rdExp e q
def rdMatch : AMatch → Path → Ty
  | .mk mr _, 0 :: q => rdMRule mr q
  | .mk _ rest, 1 :: q => rdMatchOpt rest q
  | _, _ => default
def rdMatchOpt : Option AMatch → Path → Ty
  | none, _ => default
  | some m, q => rdMatch m q
def rdMRule : AMRule → Path → Ty
  | .mk p _, 0 :: q => rdPat p q
  | .mk _ e, 1 :: q => rdExp e q
  | _, _ => default
def rdDec : ADec → Path → Ty
  | .val _ vb, 0 :: q => rdValBind vb q
  | _, _ => default
def rdValBind : AValBind → Path → Ty
  | .var _ _ τ _ _, [0] => hN τ
  | .var _ _ _ e _, 1 :: q => rdExp e q
  | .var _ _ _ _ rest, 2 :: q => rdValBindOpt rest q
  | .pat p _, 0 :: q => rdAtPat p q
  | .pat _ e, 1 :: q => rdExp e q
  | _, _ => default
def rdValBindOpt : Option AValBind → Path → Ty
  | none, _ => default
  | some vb, q => rdValBind vb q
end

def rdTop : ATopDec → Path → Ty
  | .value _ vb, 0 :: q => rdValBind vb q
  | .seq a1 _, 0 :: q => rdTop a1 q
  | .seq _ a2, 1 :: q => rdTop a2 q
  | _, _ => default

end StandardElm.Stat.Complete
