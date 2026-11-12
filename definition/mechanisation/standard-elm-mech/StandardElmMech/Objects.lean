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
  * Effect values (EffVal, effects.tex fig:effects-compound) are constructors of `Val` (plan
    decision D5): tasks, process identifiers, commands and subscriptions (leaves, batches, maps),
    programs, and JSON values (`bv`).
  * Floats are Lean's `Float` (IEEE 754 binary64); characters are Lean's
    `Char` with code = Unicode scalar value; strings are Lean's `String`.
-/
import StandardElmMech.Syntax
import StandardElmMech.Eff.PTy
import StandardElmMech.Eff.Boundary

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
  deriving Repr, Inhabited, DecidableEq

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
  /-- Elm.Kernel.Basics.log, used by the text of logBase (fig:dynamic-basis-elem) -/
  | kernelLog
  /-- record(l1 ... ln), n ≥ 1: the constructor of a record alias (sec:dynamic-modules-record) -/
  | record (ls : List String)
  /-- the values of ports (sec:effects-ports); APPLY is step 4's -/
  | outport (p : String) (τ : Eff.PTy)
  | inport (p : String) (τ : Eff.PTy)
  /-- Platform.Cmd.batch, Platform.Cmd.map, Platform.Sub.batch, Platform.Sub.map, Platform.worker
      (fig:effects-apply) -/
  | cmdBatch | cmdMap | subBatch | subMap | platformWorker
  /-- Task.succeed, Task.fail, Task.andThen, Task.onError, Task.command, Process.sleep,
      Process.spawn, Process.kill (fig:effects-apply); Array.fromList, Array.toList
      (sec:appendix-dynamic-basis-arrays) -/
  | taskSucceed | taskFail | taskAndThen | taskOnError | taskCommand
  | processSleep | processSpawn | processKill
  | arrayFromList | arrayToList
  deriving Repr, DecidableEq, Inhabited

/-- arity(b), from the figures of Appendix D. -/
def BasVal.arity : BasVal → Nat
  | .negate | .not | .isNaN | .isInfinite | .debugTodo => 1
  | .toFloat | .round | .floor | .ceiling | .truncate => 1
  | .sqrt | .sin | .cos | .tan | .asin | .acos | .atan => 1
  | .charToCode | .charFromCode | .debugToString => 1
  | .kernelLog | .outport .. | .inport .. | .cmdBatch | .subBatch | .platformWorker => 1
  | .taskSucceed | .taskFail | .taskCommand | .processSleep | .processSpawn | .processKill => 1
  | .arrayFromList | .arrayToList => 1
  | .record ls => ls.length
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
def conOk : Con := ⟨"Ok", 1⟩
def conErr : Con := ⟨"Err", 1⟩
/-- The hidden constructor of Never (appendix-static-basis.tex, the hidden identifiers). -/
def conJustOneMore : Con := ⟨"JustOneMore", 1⟩
/-- The harness's Html node (plan decision D2): `Html.text` is bound to it. No identifier spells
    `node#`, so it adds no kind of value and no APPLY case. -/
def conNode : Con := ⟨"node#", 1⟩
/-- arr#: the constructor of arrays (sec:appendix-dynamic-basis-arrays). -/
def conArr : Con := ⟨"arr#", 1⟩
/-- bin#: the constructor of byte sequences (sec:appendix-dynamic-basis-bytes). -/
def conBin : Con := ⟨"bin#", 1⟩
/-- The hidden constructor Perform of Task's MyCmd (sec:effects-apply). Spelt with a dot so that
    no constructor of a program has the same name (constructor names are compared by spelling). -/
def conPerform : Con := ⟨"Task.Perform", 1⟩

/-! ## Primitives and managers (fig:effects-compound) -/

/-- Prim: the primitives of Process (sec:effects-simple). Prim_plat is empty ([params]). -/
inductive Prim where
  | sleep | spawn | kill
  deriving Repr, DecidableEq, Inhabited

def Prim.arity : Prim → Nat := fun _ => 1

/-- Prim_plat: the primitives of the platform; the empty platform ([params]). -/
def platPrims : List Prim := []

/-- Mgr: the task manager, outgoing and incoming ports. Mgr_plat is empty ([params]). -/
inductive Mgr where
  | task
  | out (p : String)
  | inn (p : String) (τ : Eff.PTy)
  deriving Repr, DecidableEq, Inhabited

/-- Mgr_plat: the managers of the platform; the empty platform ([params]). -/
def platMgrs : List Mgr := []

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
    /-- batch(c1 ... cn), a command or subscription (effects.tex, fig:effects-compound); `none` is
        batch(), in CmdVal and in SubVal alike, so one constructor serves both -/
    | batch (cs : List Val)
    /-- map(v, c) -/
    | mapE (f : Val) (c : Val)
    /-- prog r, a program value (ProgVal), r the record Platform.worker is applied to -/
    | prog (r : List (String × Val))
    /-- succeed v -/
    | succeed (v : Val)
    /-- fail v -/
    | fail (v : Val)
    /-- andThen(v, tk) -/
    | andThen (f t : Val)
    /-- onError(v, tk) -/
    | onError (f t : Val)
    /-- prim(π, v1 ... vk), k the arity of π -/
    | prim (π : Prim) (args : List Val)
    /-- a process identifier (ProcId = Nat) -/
    | pid (n : Nat)
    /-- leaf(m, v); for m = out p, v is `.bv j` with j any boundary value -/
    | leaf (m : Mgr) (v : Val)
    /-- a JSON value; or, as the argument of an out leaf, a boundary value (`Val.WF`) -/
    | bv (j : Eff.BVal)
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

/-- A log: the entries `(label, value)` of the applications of Debug.log in a derivation of a
    logged relation, in the order the logged rules fix (plan decision D4, RulesL.lean). -/
abbrev Log := List (String × Val)

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

/-- E + E': both components modified. -/
def Env.plusEnv (E E' : Env) : Env := .mk (fmPlus E.QE E'.QE) (fmPlus E.VE E'.VE)

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

/-- An outcome of a task: succeed v or fail v (fig:effects-compound). -/
def Val.isOutcome : Val → Bool
  | .succeed _ | .fail _ => true
  | _ => false

/-- A task: succeed, fail, andThen, onError, prim (TaskVal, fig:effects-compound). -/
def Val.isTask : Val → Bool
  | .succeed _ | .fail _ | .andThen _ _ | .onError _ _ | .prim _ _ => true
  | _ => false
def Val.bool (b : Bool) : Val := .con (if b then conTrue else conFalse) []
abbrev Val.nil : Val := .con conNil []
abbrev Val.cons (v vs : Val) : Val := .con conCons [v, vs]
def Val.ofList : List Val → Val
  | [] => .nil
  | v :: vs => .cons v (Val.ofList vs)

/-- The elements of a list value `v1 :: ... :: vn :: []`. -/
def Val.toList? : Val → Option (List Val)
  | .con c [] => if c = conNil then some [] else none
  | .con c [h, t] => if c = conCons then (Val.toList? t).map (h :: ·) else none
  | _ => none

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
