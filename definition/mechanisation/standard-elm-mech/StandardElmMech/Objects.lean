/-
  A Standard Definition of Elm? Mechanisation, part 2.
  Semantic objects of the Core dynamic semantics:
  Figure fig:dynamic-core-simple (SVal, BasVal, Con, FAIL) and
  Figure fig:dynamic-core-compound (Val, BasApp, ConVal, Record, Tuple,
  Closure, Env, QualEnv, ValEnv), with the operation Rec of
  sec:dynamic-core-closures and the free variables FV of a value binding.

  Encoding choices (see README):
  * Finite maps are association lists; lookup takes the first binding, and
    modification `f + g` puts `g` first and drops the keys of `g` from `f`.
  * A constructor name carries its arity (`Con`), which the book says
    elaboration determines ("arity(con) always means the arity of con in the
    custom type of the value at hand").
  * Effect values (EffVal) are omitted: they belong to Chapter 8.
  * Floats are Lean's `Float` (IEEE 754 binary64); characters are Lean's
    `Char` with code = Unicode scalar value; strings are Lean's `String`.
-/
import StandardElmMech.Syntax

namespace StandardElm

/-! ## Int range and normalisation (Appendix E, sec:appendix-implementation-int)

  The definition is parameterised by IntRange and norm. We fix eco's choice:
  IntRange = [-2^63, 2^63 - 1] and norm = wrap modulo 2^64. -/

def intMin : Int := -(2 ^ 63)
def intMax : Int := 2 ^ 63 - 1
/-- norm(n): the m in IntRange with m = n (mod 2^64). -/
@[irreducible] def norm (n : Int) : Int := (n + 2 ^ 63) % (2 ^ 64) - 2 ^ 63

/-! ## Simple objects -/

/-- SVal: special values (Int values, floats, characters, strings). -/
inductive SVal where
  | int (n : Int)
  | float (x : Float)
  | char (c : Char)
  | str (s : String)
  deriving Repr, Inhabited

/-- BasVal: the basic values of the fragment (Appendix D,
    fig:dynamic-basis-basics, fig:dynamic-basis-operators,
    fig:dynamic-basis-others). The operators' variables (add, sub, ...)
    are named as in fig:dynamic-basis-operators. -/
inductive BasVal where
  | add | sub | mul | fdiv | idiv | pow
  | modBy | remainderBy | negate
  | eq | neq
  | compare | lt | gt | le | ge | min | max | clamp
  | not | and | or | xor
  | isNaN | isInfinite
  | toFloat | round | floor | ceiling | truncate
  | sqrt | sin | cos | tan | asin | acos | atan | atan2
  | append | charToCode | charFromCode
  | debugLog | debugTodo | debugToString
  deriving Repr, DecidableEq, Inhabited

/-- arity(b), from the figures of Appendix D. -/
def BasVal.arity : BasVal → Nat
  | .negate | .not | .isNaN | .isInfinite | .debugTodo => 1
  | .toFloat | .round | .floor | .ceiling | .truncate => 1
  | .sqrt | .sin | .cos | .tan | .asin | .acos | .atan => 1
  | .charToCode | .charFromCode | .debugToString => 1
  | .clamp => 3
  | _ => 2

/-- Con: constructor names. A constructor name is identified by its spelling
    and carries its arity in its custom type. `[]` and `::` are the two list
    constructor names that no identifier spells. -/
structure Con where
  name : String
  arity : Nat
  deriving Repr, DecidableEq, Inhabited

def conNil : Con := ⟨"[]", 0⟩
def conCons : Con := ⟨"::", 2⟩
def conTrue : Con := ⟨"True", 0⟩
def conFalse : Con := ⟨"False", 0⟩
def conLT : Con := ⟨"LT", 0⟩
def conEQ : Con := ⟨"EQ", 0⟩
def conGT : Con := ⟨"GT", 0⟩
def conJust : Con := ⟨"Just", 1⟩
def conNothing : Con := ⟨"Nothing", 0⟩

/-! ## Compound objects (fig:dynamic-core-compound) -/

mutual
  /-- Val = {()} + SVal + BasApp + ConVal + Record + Tuple + Closure
      (EffVal omitted). -/
  inductive Val where
    | unit                                            -- ()
    | sv (s : SVal)                                   -- special value
    | basApp (b : BasVal) (args : List Val)           -- (b, v1 ... vk), k < arity b
    | con (c : Con) (args : List Val)                 -- con v1 ... vk, k <= arity con
    | record (r : List (String × Val))                -- Lab -fin-> Val
    | tuple (v1 v2 : Val) (v3 : Option Val)           -- (v1, v2 [, v3])
    | closure (p : AtPat) (e : Exp) (E : Env) (VE : List (String × Val))  -- (atpat, exp, E, VE)
  /-- (All three finite maps are written `List (String × _)` because the
      kernel's nested-inductive translation needs syntactically equal
      occurrences; Lab, Ident and ModId are all `String`.)
      Env = QualEnv x ValEnv, QualEnv = ModId -fin-> Env,
      ValEnv = (Var + Con) -fin-> Val. -/
  inductive Env where
    | mk (QE : List (String × Env)) (VE : List (String × Val))
end

instance : Inhabited Val := ⟨.unit⟩
instance : Inhabited Env := ⟨.mk [] []⟩

abbrev ValEnv := List (Ident × Val)
abbrev Record := List (Lab × Val)

def Env.QE : Env → List (ModId × Env) | .mk q _ => q
def Env.VE : Env → ValEnv | .mk _ v => v

/-! ## Finite maps -/

def fmLookup {α β} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k, v) :: rest, a => if k == a then some v else fmLookup rest a

def fmDom {α β} (f : List (α × β)) : List α := f.map (·.1)

/-- f + g: g's bindings replace f's. -/
def fmPlus {α β} [BEq α] (f g : List (α × β)) : List (α × β) :=
  g ++ f.filter (fun p => !(g.any (fun q => q.1 == p.1)))

/-- E + VE means E + (empty, VE). -/
def Env.plusVE (E : Env) (VE : ValEnv) : Env := .mk E.QE (fmPlus E.VE VE)

/-- E(id) and E(modid.id): lookup of a long identifier
    (sec:dynamic-core-compound). -/
def Env.lookup (E : Env) (li : LongId) : Option Val :=
  match li.qual with
  | none => fmLookup E.VE li.id
  | some m =>
    match fmLookup E.QE m with
    | some E' => fmLookup E'.VE li.id
    | none => none

/-! ## Rec (sec:dynamic-core-closures) -/

/-- Rec VE: each closure in Ran VE gets VE as its fourth component. -/
def recVE (VE : ValEnv) : ValEnv :=
  VE.map fun (x, v) =>
    match v with
    | .closure p e E _ => (x, .closure p e E VE)
    | v => (x, v)

/-! ## VE/FAIL and v/FAIL -/

/-- VE/FAIL: a value environment or FAIL. -/
inductive VEF where
  | ok (VE : ValEnv)
  | fail
  deriving Inhabited

/-- VE + FAIL = FAIL + VE = FAIL + FAIL = FAIL. -/
def VEF.plus : VEF → VEF → VEF
  | .ok a, .ok b => .ok (fmPlus a b)
  | _, _ => .fail

/-- v/FAIL: a value or FAIL. -/
inductive VF where
  | ok (v : Val)
  | fail
  deriving Inhabited

/-! ## Helpers on values -/

abbrev Val.int (n : Int) : Val := .sv (.int n)
def Val.bool (b : Bool) : Val := .con (if b then conTrue else conFalse) []
abbrev Val.nil : Val := .con conNil []
abbrev Val.cons (v vs : Val) : Val := .con conCons [v, vs]
def Val.ofList : List Val → Val
  | [] => .nil
  | v :: vs => .cons v (Val.ofList vs)

/-! ## Free variables (sec:appendix-derived-forms-let)

  An occurrence of a variable is free if it is unqualified and not within the
  scope of a binding of it made inside the phrase. FV(valbind) is the set of
  variables free in the right-hand sides of valbind. -/

mutual
  def boundAtPat : AtPat → List Var
    | .var x => [x]
    | .tuple p1 p2 p3 => boundPat p1 ++ boundPat p2 ++ boundPatOpt p3
    | .record r => boundPatRowOpt r
    | .paren p => boundPat p
    | _ => []
  def boundPatOpt : Option Pat → List Var
    | none => []
    | some p => boundPat p
  def boundPatRowOpt : Option PatRow → List Var
    | none => []
    | some r => boundPatRow r
  def boundPatRow : PatRow → List Var
    | .field l r => l :: boundPatRowOpt r
  def boundPat : Pat → List Var
    | .atpat a => boundAtPat a
    | .con _ args => boundAtPats args
    | .cons p1 p2 => boundPat p1 ++ boundPat p2
    | .as p x => x :: boundPat p
  def boundAtPats : List AtPat → List Var
    | [] => []
    | a :: as => boundAtPat a ++ boundAtPats as
end

mutual
  /-- Variables bound by a value binding (the domain of its VE). -/
  def boundValBind : ValBind → List Var
    | .var x _ rest => x :: boundValBindOpt rest
    | .pat p _ => boundAtPat p
  def boundValBindOpt : Option ValBind → List Var
    | none => []
    | some vb => boundValBind vb
end

def removeAll (xs ys : List Var) : List Var := xs.filter (fun x => !(ys.contains x))

mutual
  def fvAtExp : AtExp → List Var
    | .var ⟨none, x⟩ => [x]
    | .tuple e1 e2 e3 => fvExp e1 ++ fvExp e2 ++ fvExpOpt e3
    | .record r => fvExpRowOpt r
    | .update x r => x :: fvExpRow r
    | .letE (.val vb) e => removeAll (fvValBindRhs vb ++ fvExp e) (boundValBind vb)
    | .paren e => fvExp e
    | _ => []
  def fvExpOpt : Option Exp → List Var
    | none => []
    | some e => fvExp e
  def fvExpRow : ExpRow → List Var
    | .field _ e r => fvExp e ++ fvExpRowOpt r
  def fvExpRowOpt : Option ExpRow → List Var
    | none => []
    | some r => fvExpRow r
  def fvExp : Exp → List Var
    | .atexp a => fvAtExp a
    | .app e a => fvExp e ++ fvAtExp a
    | .lam p e => removeAll (fvExp e) (boundAtPat p)
    | .caseE e m => fvExp e ++ fvMatch m
  def fvMatch : Match → List Var
    | .mk (.mk p e) rest => removeAll (fvExp e) (boundPat p) ++ fvMatchOpt rest
  def fvMatchOpt : Option Match → List Var
    | none => []
    | some m => fvMatch m
  /-- FV(valbind): variables free in the right-hand sides. -/
  def fvValBindRhs : ValBind → List Var
    | .var _ e rest => fvExp e ++ fvValBindRhsOpt rest
    | .pat _ e => fvExp e
  def fvValBindRhsOpt : Option ValBind → List Var
    | none => []
    | some vb => fvValBindRhs vb
end

/-- The side condition of r:d-dec-nonrec / r:d-dec-rec:
    is Dom VE intersected with FV(valbind) non-empty? -/
def isRecursive (VE : ValEnv) (vb : ValBind) : Bool :=
  (fmDom VE).any (fun x => (fvValBindRhs vb).contains x)

end StandardElm
