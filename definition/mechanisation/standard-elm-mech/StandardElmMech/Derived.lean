/-
  A Standard Definition of Elm? Mechanisation, part 7.
  Derived forms (Appendix A, appendix-derived-forms.tex) as functions that
  build the equivalent bare phrase, so that examples can be written close to
  their full syntax. Each function names the row of the appendix it encodes.
  The grouping of the definitions of a let
  (sec:appendix-derived-forms-let) is computed: "refers to", components,
  and an order in which every component follows those it refers to.
-/
import StandardElmMech.Objects

namespace StandardElm.D
open StandardElm

/-! ## Identifiers and constants -/

/-- `True`, `False` and `negate` of the equivalent forms are those of the
    initial basis, written qualified by Basics (sec:appendix-dynamic-basis-elm). -/
def basicsTrue : LongId := ⟨some "Basics", "True"⟩
def basicsFalse : LongId := ⟨some "Basics", "False"⟩
def basicsNegate : LongId := ⟨some "Basics", "negate"⟩

/-- A variable as an atomic expression. -/
def vA (x : String) : AtExp := .var ⟨none, x⟩
/-- A variable as an expression. -/
def v (x : String) : Exp := .atexp (vA x)
/-- A qualified variable. -/
def qv (m x : String) : Exp := .atexp (.var ⟨some m, x⟩)
/-- A constructor. -/
def cA (k : String) : AtExp := .con ⟨none, k⟩
def c (k : String) : Exp := .atexp (cA k)
/-- An integer constant at Int (n >= 0). -/
def litA (n : Nat) : AtExp := .scon (.int n)
/-- A character and a string constant. -/
def chA (ch : Char) : AtExp := .scon (.char ch)
def strA (s : String) : AtExp := .scon (.str s)
def str (s : String) : Exp := .atexp (strA s)

/-- Row "-atexp": `-atexp` is `(negate atexp)`. -/
def neg (a : AtExp) : AtExp := .paren (.app (.atexp (.var basicsNegate)) a)

/-- An integer as written in the source: a constant, or the negation of one. -/
def iA (n : Int) : AtExp := if n < 0 then neg (litA n.natAbs) else litA n.natAbs
def i (n : Int) : Exp := .atexp (iA n)

/-- Parenthesise an expression to use it where an atomic one is needed; an
    atomic expression is used as it stands. -/
def A : Exp → AtExp
  | .atexp a => a
  | e => .paren e

instance : Coe AtExp Exp := ⟨.atexp⟩

/-- Application `f a1 ... an` (left associative). -/
def ap (f : Exp) (args : List Exp) : Exp := args.foldl (fun acc a => .app acc (A a)) f

/-! ## Expressions (fig:appendix-derived-forms-expressions) -/

/-- Row "exp1 opv exp2": `(opv) (exp1) (exp2)`, for opv other than && and ||. -/
def bin (o : Op) (e1 e2 : Exp) : Exp := .app (.app (.atexp (.op o)) (.paren e1)) (.paren e2)

/-- Row "if exp1 then exp2 else exp3":
    `case exp1 of True -> (exp2) ; False -> exp3`. -/
def ifte (e1 e2 e3 : Exp) : Exp :=
  .caseE e1 (.mk (.mk (.atpat (.con basicsTrue)) (.atexp (.paren e2)))
                 (some (.mk (.mk (.atpat (.con basicsFalse)) e3) none)))

/-- Row "exp1 && exp2": `if exp1 then exp2 else False`. -/
def andalso (e1 e2 : Exp) : Exp := ifte e1 e2 (.atexp (.con basicsFalse))
/-- Row "exp1 || exp2": `if exp1 then True else exp2`. -/
def orelse (e1 e2 : Exp) : Exp := ifte e1 (.atexp (.con basicsTrue)) e2

/-- Row "\atpat1 ... atpatn -> exp": nested lambdas (n >= 1). -/
def lams (ps : List AtPat) (e : Exp) : Exp := ps.foldr (fun p acc => .lam p acc) e

/-- Row "[exp1, ..., expn]": `(exp1 :: ... :: expn :: [ ])`, each :: infixed
    and grouped to the right; `[ ]` itself is bare. -/
def listE : List Exp → Exp
  | [] => .atexp .nil
  | es => .atexp (.paren (es.foldr (fun e acc => bin "::" e acc) (.atexp .nil)))

/-- Row ".lab": `(\{ lab } -> lab)`. -/
def accessor (l : Lab) : AtExp :=
  .paren (.lam (.record (some (.field l none))) (.atexp (.var ⟨none, l⟩)))

/-- Row "atexp.lab": `(.lab atexp)`. -/
def access (a : AtExp) (l : Lab) : AtExp := .paren (.app (.atexp (accessor l)) a)

/-- Record expression `{ lab1 = exp1, ..., labn = expn }` (bare). -/
def recE : List (Lab × Exp) → Exp
  | [] => .atexp (.record none)
  | fs => .atexp (.record (some (rowOf fs)))
where
  rowOf : List (Lab × Exp) → ExpRow
    | [] => .field "" (.atexp .unit) none   -- not reached
    | [(l, e)] => .field l e none
    | (l, e) :: rest => .field l e (some (rowOf rest))

/-- Record update `{ x | lab1 = exp1, ... }` (bare). -/
def updE (x : Var) (fs : List (Lab × Exp)) : Exp := .atexp (.update x (recE.rowOf fs))

/-- Tuples (bare). -/
def tup2 (a b : Exp) : Exp := .atexp (.tuple a b none)
def tup3 (a b c : Exp) : Exp := .atexp (.tuple a b (some c))

/-- `case exp of p1 -> e1 ; ... ; pn -> en` (bare). -/
def caseOf (e : Exp) (rules : List (Pat × Exp)) : Exp := .caseE e (mOf rules)
where
  mOf : List (Pat × Exp) → Match
    | [] => .mk (.mk (.atpat .wild) (.atexp .unit)) none   -- not reached
    | [(p, b)] => .mk (.mk p b) none
    | (p, b) :: rest => .mk (.mk p b) (some (mOf rest))

/-- `Debug.log "label" (exp)`. -/
def debugLog (label : String) (e : Exp) : Exp :=
  .app (.app (qv "Debug" "log") (strA label)) (.paren e)

/-! ## Patterns (fig:appendix-derived-forms-patterns) -/

def pv (x : Var) : AtPat := .var x
def pw : AtPat := .wild
def pcA (k : String) : AtPat := .con ⟨none, k⟩
/-- A constructed pattern `Con atpat1 ... atpatn`. -/
def pcon (k : String) (args : List AtPat) : Pat :=
  if args.isEmpty then .atpat (pcA k) else .con ⟨none, k⟩ args
def pint (n : Nat) : AtPat := .scon (.int n)
def pchar (ch : Char) : AtPat := .scon (.char ch)
def P (a : AtPat) : Pat := .atpat a
/-- A pattern used where an atomic pattern is needed. -/
def PA : Pat → AtPat
  | .atpat a => a
  | p => .paren p
def ptup2 (a b : Pat) : AtPat := .tuple a b none
def ptup3 (a b c : Pat) : AtPat := .tuple a b (some c)
def precord (ls : List Lab) : AtPat := .record (rowOf ls)
where
  rowOf : List Lab → Option PatRow
    | [] => none
    | l :: rest => some (.field l (rowOf rest))
/-- Row "[pat1, ..., patn]": `(pat1 :: [pat2, ..., patn])`. -/
def listP : List Pat → AtPat
  | [] => .nil
  | p :: ps => .paren (.cons p (.atpat (listP ps)))

/-! ## Definitions and the grouping of a let (sec:appendix-derived-forms-let) -/

/-- A definition as written: `var atpat1 ... atpatm = exp` (m >= 0), or
    `atpat = exp`. -/
inductive Def where
  | fn (x : Var) (ps : List AtPat) (e : Exp)
  | pat (p : AtPat) (e : Exp)
  deriving Inhabited

/-- The variables bound by a definition. -/
def Def.bound : Def → List Var
  | .fn x _ _ => [x]
  | .pat p _ => boundAtPat p

/-- The right-hand side of a definition. -/
def Def.rhs : Def → Exp
  | .fn _ ps e => lams ps e
  | .pat _ e => e

/-- d_i refers to d_j if a variable bound by d_j occurs free in the
    right-hand side of d_i. -/
def refers (ds : List Def) (i j : Nat) : Bool :=
  let fv := fvExp (ds[i]!).rhs
  (ds[j]!).bound.any (fun x => fv.contains x)

/-- Reachability by zero or more steps of "refers to". -/
def reach (ds : List Def) : Nat → Nat → Bool := Id.run do
  let n := ds.length
  let mut m : Array (Array Bool) :=
    Array.ofFn (n := n) fun a => Array.ofFn (n := n) fun b => a.val == b.val || refers ds a.val b.val
  for k in List.range n do
    for a in List.range n do
      for b in List.range n do
        if m[a]![k]! && m[k]![b]! then
          m := m.set! a (m[a]!.set! b true)
  return fun a b => m[a]![b]!

/-- The components, each as its member indices in increasing order, in an
    order in which a component comes after every component it refers to;
    among the components ready to be placed the one with the least member
    comes first. -/
def components (ds : List Def) : List (List Nat) := Id.run do
  let n := ds.length
  let r := reach ds
  let comps : List (List Nat) :=
    (List.range n).foldl (fun acc a =>
      if acc.any (fun cmp => cmp.contains a) then acc
      else acc ++ [(List.range n).filter (fun b => r a b && r b a)]) []
  let mut placed : List (List Nat) := []
  let mut todo := comps
  for _ in List.range (n + 1) do
    match todo.find? (fun cmp => cmp.all (fun a => (List.range n).all (fun b =>
            !(refers ds a b) || cmp.contains b || placed.any (fun p => p.contains b)))) with
    | some cmp =>
      placed := placed ++ [cmp]
      todo := todo.filter (fun x => x != cmp)
    | none => pure ()
  return placed

/-- The value binding `valbind_i1 and ... and valbind_ip` of a component.
    Row "var atpat1 ... atpatn = exp" gives `var = \atpat1 ... atpatn -> exp`. -/
def groupBind (ds : List Def) : List Nat → ValBind
  | [] => .pat .wild (.atexp .unit)     -- not reached
  | [a] => match ds[a]! with
    | .fn x ps e => .var x (lams ps e) none
    | .pat p e => .pat p e
  | a :: rest => match ds[a]! with
    | .fn x ps e => .var x (lams ps e) (some (groupBind ds rest))
    | .pat p e => .pat p e                 -- a destructuring binding is never in a recursive component

/-- Row "let valbind1 ... valbindn in exp" (n >= 2), and the bare
    `let valbind in exp` for n = 1. -/
def letDefs (ds : List Def) (body : Exp) : Exp :=
  (components ds).foldr (fun cmp acc => .atexp (.letE (.val (groupBind ds cmp)) acc)) body

end StandardElm.D
