/-
  A Standard Definition of Elm? Mechanisation: the source syntax, plan step 8.

  Every program elm-syntax parses, as written (Figures fig:core-grammar-* and fig:grammar-modules),
  with operator chains as elm-syntax groups them by the fixities of Figure fig:core-fixities (the
  `[parse]` trust), type expressions, annotations, custom types, aliases, ports, headers and
  imports. Constants are kept as decoded, before number specialisation: an integer by its value
  before `norm`, a float as m × 10^e as written. No source positions are kept. Sequences are lists
  (nested inductives); every function over these types is structurally recursive, so that the
  kernel reduces it.
-/
import StandardElmMech.Syntax

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

/-- A special constant as written (sec:syntax-core-constants), before number specialisation. -/
inductive SLit where
  | int (n : Nat)
  | float (m : Nat) (e : Int)
  | char (c : Char)
  | str (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- Type expressions as written (Figure fig:core-grammar-types); elm-syntax drops parentheses. -/
inductive STy where
  | var (a : String)
  | con (c : LongId) (args : List STy)
  | unit
  | tuple (ts : List STy)
  | record (fs : List (Lab × STy))
  | ext (r : String) (fs : List (Lab × STy))
  | fn (a b : STy)
  deriving Repr, Inhabited

/-- Patterns as written (Figure fig:core-grammar-patterns, with the derived list pattern). -/
inductive SPat where
  | wild
  | lit (l : SLit)
  | var (x : Var)
  | unit
  | con (k : LongId) (args : List SPat)
  | tuple (ps : List SPat)
  | list (ps : List SPat)
  | record (ls : List Lab)
  | cons (p1 p2 : SPat)
  | as (p : SPat) (x : Var)
  | paren (p : SPat)
  deriving Repr, Inhabited

mutual
/-- Expressions as written; operator applications as elm-syntax groups them ([parse]). -/
inductive SExp where
  | lit (l : SLit)
  | var (x : LongId)
  | con (k : LongId)
  | opVal (o : Op)
  | unit
  | tuple (es : List SExp)
  | list (es : List SExp)
  | record (fs : List (Lab × SExp))
  | update (x : Var) (fs : List (Lab × SExp))
  | accessor (l : Lab)
  | access (e : SExp) (l : Lab)
  | neg (e : SExp)
  | paren (e : SExp)
  | app (f : SExp) (args : List SExp)
  | binop (o : Op) (l r : SExp)
  /-- if c1 then e1 else if c2 then e2 ... else e: the maximal chain of unparenthesised ifs -/
  | ifte (arms : List (SExp × SExp)) (els : SExp)
  | lam (ps : List SPat) (body : SExp)
  | caseE (e : SExp) (rules : List (SPat × SExp))
  | letE (defs : List SDef) (body : SExp)
/-- A definition: `var [: ty] atpat1 ... atpatm = exp` (m ≥ 0) or `atpat = exp`. -/
inductive SDef where
  | fn (x : Var) (ann : Option STy) (ps : List SPat) (e : SExp)
  | pat (p : SPat) (e : SExp)
end

instance : Inhabited SExp := ⟨.unit⟩

inductive SItem where
  | var (x : Var) | op (o : Op) | ty (c : String) | tyAll (c : String)
  deriving Repr, DecidableEq, Inhabited

inductive SExposing where
  | all
  | items (is : List SItem)
  deriving Repr, DecidableEq, Inhabited

structure SImport where
  mod : ModId
  alias : Option ModId
  exposing : Option SExposing
  deriving Repr, Inhabited

inductive STopDec where
  | custom (c : String) (params : List String) (ctors : List (String × List STy))
  | alias (c : String) (params : List String) (t : STy)
  | port (x : Var) (t : STy)
  | value (d : SDef)
  deriving Inhabited

structure SHeader where
  isPort : Bool
  name : ModId
  exposing : SExposing
  deriving Inhabited

structure SModule where
  header : SHeader
  imports : List SImport
  decls : List STopDec
  deriving Inhabited

/-- A program: its modules, the main module last (sec:programs-syntax). -/
structure SProgram where
  project : String
  name : String
  modules : List SModule
  deriving Inhabited

end StandardElm.Src
