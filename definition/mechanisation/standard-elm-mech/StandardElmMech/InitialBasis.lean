/-
  A Standard Definition of Elm? Mechanisation, part 7b.
  The parts of the initial dynamic basis (Appendix D) that the rules
  themselves read: E0's value environment VE0, the environment E_K of the
  texts of Basics written in Elm, the values of those texts, and the dynamic
  operator table OT_dyn (fig:dynamic-basis-operators), which rule
  r:d-atexp-op reads.

  * VE_K binds every identifier of Basics that the figures do not mark "Elm"
    (only those of the fragment), the hidden variables of the operators
    included (add, sub, eq, ...).
  * E_K = E0 + (QE_K, VE_K), QE_K = {Basics ↦ (∅, VE_K)} (the kernel module
    Elm.Kernel.Basics, used only by logBase, is omitted).
  * Each text `var = \atpat -> exp` evaluates in E_K by r:d-dec-nonrec, through
    r:d-valbind-var and r:d-exp-lambda, to {var ↦ (atpat, exp, E_K, ∅)}; the
    values are built in that form here, and `elmText_eval` in Theorems.lean
    proves each derivation.
-/
import StandardElmMech.Derived
import StandardElmMech.Apply

namespace StandardElm
open StandardElm.D

def bas (b : BasVal) : Val := .basApp b []
def conv (c : Con) : Val := .con c []

/-- VE0 = {[] ↦ [], :: ↦ ::}. -/
def VE0 : ValEnv := [("[]", conv conNil), ("::", conv conCons)]

/-- E0 = (∅, VE0): every module is evaluated starting from it. -/
def E0base : Env := .mk [] VE0

/-- E + (QE, VE): both components modified. -/
def Env.plus (E : Env) (QE : List (String × Env)) (VE : ValEnv) : Env :=
  .mk (fmPlus E.QE QE) (fmPlus E.VE VE)

/-- The hidden variables the operators stand for (fig:dynamic-basis-operators). -/
def hiddenOpVars : ValEnv :=
  [ ("add", bas .add), ("sub", bas .sub), ("mul", bas .mul), ("fdiv", bas .fdiv),
    ("idiv", bas .idiv), ("pow", bas .pow), ("eq", bas .eq), ("neq", bas .neq),
    ("lt", bas .lt), ("gt", bas .gt), ("le", bas .le), ("ge", bas .ge),
    ("and", bas .and), ("or", bas .or) ]

/-- The basic values and constructors of Basics in the fragment
    (fig:dynamic-basis-basics); min, max (A48) and clamp (A49) are basic
    values. -/
def VE_BasicsKernel : ValEnv :=
  [ ("True", conv conTrue), ("False", conv conFalse),
    ("LT", conv conLT), ("EQ", conv conEQ), ("GT", conv conGT),
    ("compare", bas .compare), ("not", bas .not), ("xor", bas .xor),
    ("modBy", bas .modBy), ("remainderBy", bas .remainderBy), ("negate", bas .negate),
    ("min", bas .min), ("max", bas .max), ("clamp", bas .clamp),
    ("isNaN", bas .isNaN), ("isInfinite", bas .isInfinite),
    ("toFloat", bas .toFloat), ("round", bas .round), ("floor", bas .floor),
    ("ceiling", bas .ceiling), ("truncate", bas .truncate),
    ("sqrt", bas .sqrt), ("sin", bas .sin), ("cos", bas .cos), ("tan", bas .tan),
    ("asin", bas .asin), ("acos", bas .acos), ("atan", bas .atan), ("atan2", bas .atan2),
    ("e", .sv (.float fE)), ("pi", .sv (.float fPi)),
    ("append", bas .append) ]

def VE_K : ValEnv := VE_BasicsKernel ++ hiddenOpVars

def E_K : Env := E0base.plus [("Basics", .mk [] VE_K)] VE_K

/-- The texts of fig:dynamic-basis-elm in the fragment, after their derived
    forms. `composeL`, `composeR`, `apR` and `apL` are hidden variables. -/
def elmTexts : List Def :=
  [ -- abs quantifies a number variable: its default copy is at Float (sec:dynamic-core-numbers,
    -- A27), with its constant 0 a float, and number specialisation also makes its copy at Int
    .fn "abs" [pv "n"] (ifte (ap (v "lt") [v "n", .atexp (.scon (.intF 0))]) (.atexp (neg (vA "n"))) (v "n")),
    .fn "abs$Int" [pv "n"] (ifte (ap (v "lt") [v "n", i 0]) (.atexp (neg (vA "n"))) (v "n")),
    .fn "composeL" [pv "g", pv "f", pv "x"] (ap (v "g") [ap (v "f") [v "x"]]),
    .fn "composeR" [pv "f", pv "g", pv "x"] (ap (v "g") [ap (v "f") [v "x"]]),
    .fn "apR" [pv "x", pv "f"] (ap (v "f") [v "x"]),
    .fn "apL" [pv "f", pv "x"] (ap (v "f") [v "x"]),
    .fn "identity" [pv "x"] (v "x"),
    .fn "always" [pv "a", pw] (v "a") ]

/-- The value a text `var atpat1 ... atpatn = exp` (n >= 1) has in E_K:
    the closure (atpat1, \atpat2 ... atpatn -> exp, E_K, ∅). -/
def elmTextValue : Def → Option (Var × Val)
  | .fn x (p :: ps) e => some (x, .closure p (lams ps e) E_K [])
  | _ => none

def VE_elm : ValEnv := elmTexts.filterMap elmTextValue

/-- OT_dyn: each operator of the fragment to the value of the identifier it
    stands for (fig:dynamic-basis-operators). `++` is `append`, which Basics
    exposes. -/
def OTdyn (o : Op) : Option Val :=
  match o with
  | "::" => some (conv conCons)
  | "+" => fmLookup hiddenOpVars "add"
  | "-" => fmLookup hiddenOpVars "sub"
  | "*" => fmLookup hiddenOpVars "mul"
  | "/" => fmLookup hiddenOpVars "fdiv"
  | "//" => fmLookup hiddenOpVars "idiv"
  | "^" => fmLookup hiddenOpVars "pow"
  | "++" => fmLookup VE_BasicsKernel "append"
  | "==" => fmLookup hiddenOpVars "eq"
  | "/=" => fmLookup hiddenOpVars "neq"
  | "<" => fmLookup hiddenOpVars "lt"
  | ">" => fmLookup hiddenOpVars "gt"
  | "<=" => fmLookup hiddenOpVars "le"
  | ">=" => fmLookup hiddenOpVars "ge"
  | "&&" => fmLookup hiddenOpVars "and"
  | "||" => fmLookup hiddenOpVars "or"
  | "<<" => fmLookup VE_elm "composeL"
  | ">>" => fmLookup VE_elm "composeR"
  | "|>" => fmLookup VE_elm "apR"
  | "<|" => fmLookup VE_elm "apL"
  | _ => none

end StandardElm
