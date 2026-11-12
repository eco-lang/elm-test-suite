/-
  A Standard Definition of Elm? Mechanisation: inhabitants, coverage and the pattern decider of
  decision D12, plan step 9 (section 9). sec:static-core-further of static-core.tex; A31, A97, B2.

  Inhabitants (A97) are possibly infinite, so they are encoded as position maps: a node at each
  position of a prefix-closed set of paths of argument indices. `unit`, tuples, `[]` and `::` are
  the constructors of the built-in type names (unit, Tuple2, Tuple3, List), so a node is a
  constant, `other` (the constants no pattern lists, in mode `exh` only), a constructor with its
  arity, or `wild` (an inhabitant of a type with no constructors and no constants).

  Patterns are normalised: a wildcard (also a variable, a record pattern), a constant by its
  denotation (A31: an integer constant by its value as an Int under `norm`), or a constructor with
  its type name. The decider is Maranget's usefulness algorithm on matrices with column types.
-/
import StandardElmMech.Stat.Annotated
import StandardElmMech.Objects

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (SLit)

/-! ## Constructors (sec:static-core-further) -/

/-- The constructors of a type name: name, argument types and result type, both over the scheme's
    bound variables (`bnd`). -/
abbrev ConTable := List (TyName × List (String × List Ty × Ty))

/-- Split a constructor's type τ1 → ... → τn → τ' t into its arguments and result. -/
def splitCon : Ty → List Ty × Ty
  | .fn a b => let (as, r) := splitCon b; (a :: as, r)
  | τ => ([], τ)

/-- The constructors a type environment gives (the type structures of custom types). -/
def conTableOfTE (TE : TyEnv) : ConTable :=
  TE.filterMap fun p =>
    match p.2.1.name? with
    | some t =>
      let cs := p.2.2.filterMap fun b =>
        if b.2.2 == .c then some (b.1, splitCon b.2.1.body) else none
      if cs.isEmpty then none else some (t, cs)
    | none => none

/-- The constructors of the built-in type names: unit, pairs, triples and lists (List from E0). -/
def builtinCons : ConTable :=
  [(tUnit, [("()", [], tUnitTy)]),
   (tTuple2, [("(,)", [.var (.bnd 0 .any), .var (.bnd 1 .any)], .con [.var (.bnd 0 .any), .var (.bnd 1 .any)] tTuple2)]),
   (tTuple3, [("(,,)", [.var (.bnd 0 .any), .var (.bnd 1 .any), .var (.bnd 2 .any)],
      .con [.var (.bnd 0 .any), .var (.bnd 1 .any), .var (.bnd 2 .any)] tTuple3)])] ++
  conTableOfTE E0.TE

/-- The constructor table of a module: the built-in names, every interface of the basis, and the
    module's own environment (its custom types, private ones included). First entry wins. -/
def conTable (B : SBasis) (E : Env) : ConTable :=
  builtinCons ++ conTableOfTE E.TE ++ (E.QE.flatMap fun p => conTableOfTE p.2.TE) ++
    (B.ME.flatMap fun p => conTableOfTE p.2.TE)

def ConTable.ctors (tbl : ConTable) (t : TyName) : List (String × List Ty × Ty) :=
  ((tbl.find? (·.1 == t)).map (·.2)).getD []

/-- The argument types of constructor k at the type τ: its scheme's result matched against τ. -/
def argTys (tbl : ConTable) (τ : Ty) (k : String) : Option (List Ty) :=
  match τ with
  | .con args t =>
    match (tbl.ctors t).find? (·.1 == k) with
    | some (_, as, .con xs _) =>
      let vs : List BVar := xs.filterMap fun x => match x with
        | .var a => some (.ty a)
        | .record [] (some e) => some (.row e)
        | _ => none
      if vs.length = xs.length then
        match bindSubst vs args with
        | some S => as.mapM S.apply
        | none => none
      else none
    | _ => none
  | _ => none

/-! ## Constants (A31, B2) -/

/-- What a constant denotes, as a pattern. -/
inductive Den where
  | int (v : Int)
  | char (c : Char)
  | str (s : String)
  deriving DecidableEq, Repr

def denote : SLit → Option Den
  | .int n => some (.int (norm n))
  | .char c => some (.char c)
  | .str s => some (.str s)
  | .float _ _ => none

/-- exh: the clause "no set of special constants covers every inhabitant of Int, Char or String"
    (res:core-exhaustiveness) is in force; irr: it is not (res:core-irredundancy). -/
inductive Mode where
  | exh | irr
  deriving DecidableEq, Repr

/-- The literal type a type is: 0 Int, 1 Char, 2 String. -/
def litKind : Ty → Option Nat
  | .con [] t => if t == tInt then some 0 else if t == tChar then some 1 else if t == tString then some 2 else none
  | _ => none

def Den.kind : Den → Nat
  | .int _ => 0 | .char _ => 1 | .str _ => 2

/-- A constant of Int is in IntRange; every Char and String is a value. -/
def Den.inRange : Den → Bool
  | .int v => decide (intMin ≤ v ∧ v ≤ intMax)
  | _ => true

/-- The number of constants of a literal kind, when finite ([params]: IntRange, Lean's Char). -/
def litDomainSize : Nat → Option Nat
  | 0 => some (intMax - intMin + 1).toNat
  | 1 => some 1112064
  | _ => none

/-! ## Inhabitants (A97), as position maps -/

abbrev Pos := List Nat

inductive INode where
  | den (d : Den)
  | other
  | con (k : String) (n : Nat)
  | wild
  deriving DecidableEq, Repr

def INode.arity : INode → Nat
  | .con _ n => n
  | _ => 0

structure Inh where
  f : Pos → Option INode

def Inh.sub (h : Inh) (i : Nat) : Inh := ⟨fun p => h.f (i :: p)⟩

/-- The constructors of τ that apply at τ: those whose argument types τ gives. -/
def ctorsAt (tbl : ConTable) (τ : Ty) : List (String × List Ty) :=
  match τ with
  | .con _ t => (tbl.ctors t).filterMap fun c => (argTys tbl τ c.1).map (c.1, ·)
  | _ => []

/-- The clause of sec:static-core-further that gives a node of an inhabitant of τ. -/
def Clause (tbl : ConTable) (mode : Mode) (τ : Ty) : INode → Prop
  | .den d => litKind τ = some d.kind ∧ d.inRange = true
  | .other => mode = .exh ∧ (litKind τ).isSome
  | .con k n => (litKind τ).isNone ∧ ∃ as, argTys tbl τ k = some as ∧ as.length = n
  | .wild => (litKind τ).isNone ∧ ctorsAt tbl τ = []

/-- h is an inhabitant of τ to depth n: a node given by a clause at the root, no child beyond its
    arity, and each child an inhabitant of its argument type to depth n - 1. -/
def IsInhN (tbl : ConTable) (mode : Mode) : Nat → Ty → Inh → Prop
  | 0, _, _ => True
  | n + 1, τ, h =>
    ∃ nd, h.f [] = some nd ∧ Clause tbl mode τ nd ∧
      (∀ i p, nd.arity ≤ i → h.f (i :: p) = none) ∧
      ∀ k as, nd = .con k as.length → argTys tbl τ k = some as →
        ∀ i (hi : i < as.length), IsInhN tbl mode n as[i] (h.sub i)

/-- h is an inhabitant of τ (coinductively: at every depth). -/
def IsInh (tbl : ConTable) (mode : Mode) (τ : Ty) (h : Inh) : Prop := ∀ n, IsInhN tbl mode n τ h

/-! ## Normalised patterns and coverage -/

inductive PatN where
  | wild
  | den (d : Den)
  | con (k : String) (args : List PatN)
  deriving Repr, Inhabited

mutual
/-- p covers h (sec:static-core-further): a wildcard everything, a constant the same denotation,
    a constructor pattern a node of that constructor whose children its arguments cover. -/
def PatN.covers : PatN → Inh → Prop
  | .wild, _ => True
  | .den d, h => h.f [] = some (.den d)
  | .con k args, h => h.f [] = some (.con k args.length) ∧ PatN.coversArgs args h 0
def PatN.coversArgs : List PatN → Inh → Nat → Prop
  | [], _, _ => True
  | p :: ps, h, i => PatN.covers p (h.sub i) ∧ PatN.coversArgs ps h (i + 1)
end

mutual
def normAtPat : AAtPat → PatN
  | .wild _ | .var _ _ | .record _ _ => .wild
  | .scon sc _ => match denote sc with
    | some d => .den d
    | none => .wild
  | .con lc _ _ => .con lc.id []
  | .unit => .con "()" []
  | .tuple p1 p2 none => .con "(,)" [normPat p1, normPat p2]
  | .tuple p1 p2 (some p3) => .con "(,,)" [normPat p1, normPat p2, normPat p3]
  | .nil _ => .con "[]" []
  | .paren p => normPat p
def normPat : APat → PatN
  | .atpat a => normAtPat a
  | .con lc _ args _ => .con lc.id (normAtPats args)
  | .cons p1 p2 => .con "::" [normPat p1, normPat p2]
  | .as p _ => normPat p
def normAtPats : List AAtPat → List PatN
  | [] => []
  | a :: as => normAtPat a :: normAtPats as
end

/-! ## Usefulness (Maranget) -/

def PatN.isWild : PatN → Bool
  | .wild => true
  | _ => false

/-- The rows of P whose first pattern covers constructor k (arity n), with that pattern replaced
    by its arguments. -/
def specializeCon (k : String) (n : Nat) : List (List PatN) → List (List PatN)
  | [] => []
  | (.wild :: r) :: P => (List.replicate n .wild ++ r) :: specializeCon k n P
  | (.con k' args :: r) :: P => if k' = k then (args ++ r) :: specializeCon k n P else specializeCon k n P
  | _ :: P => specializeCon k n P

def specializeDen (d : Den) : List (List PatN) → List (List PatN)
  | [] => []
  | (.wild :: r) :: P => r :: specializeDen d P
  | (.den d' :: r) :: P => if d' = d then r :: specializeDen d P else specializeDen d P
  | _ :: P => specializeDen d P

/-- The default matrix: the rows whose first pattern is a wildcard. -/
def defaultM : List (List PatN) → List (List PatN)
  | [] => []
  | (.wild :: r) :: P => r :: defaultM P
  | _ :: P => defaultM P

def headCons (P : List (List PatN)) : List String :=
  dedupL (P.filterMap fun r => match r with
    | .con k _ :: _ => some k
    | _ => none)

def headDens (P : List (List PatN)) : List Den :=
  dedupL (P.filterMap fun r => match r with
    | .den d :: _ => some d
    | _ => none)

/-- The first constant of a literal kind, of the candidates c_0 .. c_m, that is not in ds: the
    witness the default matrix needs in mode irr. For Int the candidates are intMin + i, for Char
    the characters of codes below 0xD800, for String the strings of i letters a. -/
def litCandidate : Nat → Nat → Option Den
  | 0, i => if intMin + (i : Int) ≤ intMax then some (.int (intMin + i)) else none
  | 1, i => if i < 0xD800 then some (.char (Char.ofNat i)) else none
  | _, i => some (.str (String.ofList (List.replicate i 'a')))

def missingDen (kind : Nat) (ds : List Den) : Option Den :=
  ((List.range (ds.length + 1)).filterMap (litCandidate kind)).find? fun d => !(ds.contains d)

/-- Usefulness of q with respect to P, the columns at types τs, by structural recursion on fuel:
    `none` when the fuel runs out, or when in mode irr no constant can be shown missing from a
    literal column (B2: then the column might be complete). -/
def useful (tbl : ConTable) (mode : Mode) : Nat → List Ty → List (List PatN) → List PatN → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, P, [] => some P.isEmpty
  | f + 1, τs, P, q :: qs =>
    let τ := τs.headD tUnitTy
    let τr := τs.tail
    match q with
    | .con k args =>
      match argTys tbl τ k with
      | some as => useful tbl mode f (as ++ τr) (specializeCon k args.length P) (args ++ qs)
      | none => none
    | .den d => useful tbl mode f τr (specializeDen d P) qs
    | .wild =>
      match litKind τ with
      | some kind =>
        match mode with
        | .exh => useful tbl mode f τr (defaultM P) qs
        | .irr =>
          match missingDen kind (headDens P) with
          | some _ => useful tbl mode f τr (defaultM P) qs
          | none => none
      | none =>
        let cs := ctorsAt tbl τ
        let hs := headCons P
        if !cs.isEmpty && cs.all (fun c => hs.contains c.1) then
          anyOpt cs fun c => useful tbl mode f (c.2 ++ τr) (specializeCon c.1 c.2.length P)
            (List.replicate c.2.length .wild ++ qs)
        else useful tbl mode f τr (defaultM P) qs
where
  /-- Some is true when one is, none when one is none and none is true. -/
  anyOpt {α : Type} : List α → (α → Option Bool) → Option Bool
    | [], _ => some false
    | x :: xs, g =>
      match g x with
      | some true => some true
      | some false => anyOpt xs g
      | none => none

mutual
/-- The size of a pattern (structural, so that the kernel reduces it). -/
def patSize : PatN → Nat
  | .wild => 1
  | .den _ => 1
  | .con _ args => 1 + patSizeList args
def patSizeList : List PatN → Nat
  | [] => 0
  | p :: ps => patSize p + patSizeList ps
end

def matSize (P : List (List PatN)) (q : List PatN) : Nat :=
  (P.map fun r => (r.map patSize).sum).sum + (q.map patSize).sum + q.length + 1

/-- Exhaustiveness of patterns at type τ: the wildcard is not useful after them. -/
def exhDec (tbl : ConTable) (τ : Ty) (ps : List PatN) : Bool :=
  useful tbl .exh (matSize (ps.map ([·])) [.wild] * 4 + 8) [τ] (ps.map ([·])) [.wild] == some false

/-- Irredundancy: each pattern is useful after the ones before it. -/
def irrDec (tbl : ConTable) (τ : Ty) (ps : List PatN) : Bool :=
  (List.range ps.length).all fun j =>
    let P := (ps.take j).map ([·])
    let q := [ps.getD j .wild]
    useful tbl .irr (matSize P q * 4 + 8) [τ] P q == some true

/-! ## The restrictions (res:core-irredundancy, res:core-exhaustiveness) -/

/-- Every inhabitant of τ is covered by some pattern (mode exh: `other` stands for the constants no
    pattern lists). -/
def ExhProp (tbl : ConTable) (τ : Ty) (ps : List PatN) : Prop :=
  ∀ h, IsInh tbl .exh τ h → ∃ p ∈ ps, p.covers h

/-- Each pattern covers an inhabitant of τ that no earlier one covers. -/
def IrrProp (tbl : ConTable) (τ : Ty) (ps : List PatN) : Prop :=
  ∀ j (hj : j < ps.length), ∃ h, IsInh tbl .irr τ h ∧ ps[j].covers h ∧ ∀ i (hi : i < j), ¬ (ps[i]'(by omega)).covers h

end StandardElm.Stat
