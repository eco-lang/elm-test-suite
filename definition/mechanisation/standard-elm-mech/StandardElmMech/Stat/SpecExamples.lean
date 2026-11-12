/-
  A Standard Definition of Elm? Mechanisation: number specialisation on small programs, plan step
  10 ("Tests gained", "Rulings, on small programs").

  Each example is a literal source program in the test basis `Btest`, run through the whole
  pipeline (`endToEnd`: step 8's derived forms, step 9's inference and checker, the specialisation
  and erasure of `Stat/Specialise.lean`), and a theorem by `decide +kernel` states what the book's
  rulings say of its reduced program: which copies are emitted, in which order, what the integer
  constants of a copy become (`.int` at Int, `.intF` at Float), what an occurrence refers to, the
  port, flags and kind of the program, or the refusal. The text is dynamic-core.tex,
  Section sec:dynamic-core-numbers; the rulings are A27 (a free `number` is Float; a variable bound
  by an annotation is not defaulted), A87 (number specialisation, the default copy always made) and
  A93 (every binding of a group quantifies the group's `number` variables; a vacuous one is Float).
  The choices of the plan that the book leaves open (canonical order of the variables, order of
  emission, A93's witness, record patterns) are cited as "Choices, item n" and "Issues, item n" of
  plans/lean-full-definition/step-10-end-to-end.md.

  The properties are read off the result by the readers of section "Reading a reduced program".
  The programs are written in the source syntax with the short constructors of Src/Notation.lean;
  each docstring gives the Elm text.
-/
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis
import StandardElmMech.Stat.RenameSyntax

namespace StandardElm.Stat
open StandardElm (Var ModId LongId)
open StandardElm.Src (prog mdl hdr imp val v qv i fl app bin str tc tv pv)

/-! ## Writing small programs -/

namespace SpecEx

/-- `import Html exposing (text)`. -/
def htmlText : Src.SImport := imp "Html" none (some (.items [.var "text"]))

/-- A program of one module `Main exposing (main)` that imports `Html exposing (text)`. -/
def single (n : String) (ds : List Src.STopDec) : Src.SProgram :=
  Src.canonOrder <| prog "spec" n [mdl (hdr false "Main" (.items [.var "main"])) [htmlText] ds]

/-- `main = text (Debug.toString (e))`. -/
def showMain (e : Src.SExp) : Src.STopDec :=
  val "main" none [] (app (v "text") [.paren (app (qv "Debug" "toString") [.paren e])])

/-- `-1`. -/
def neg1 : Src.SExp := .neg (i 1)

/-- `a // b`, which fixes `number` to Int. -/
def idiv (a b : Src.SExp) : Src.SExp := bin "//" a b

/-- `1.5`. -/
def f15 : Src.SExp := fl 15 (-1)

/-! ## Reading a reduced program -/

/-- The bindings of a top-level declaration, in order. -/
def topDefs : Mod.TopDec → List (Var × Exp)
  | .val vb => vb
  | .seq t1 t2 => topDefs t1 ++ topDefs t2
  | _ => []

def module? (r : Mod.Reduced) (m : ModId) : Option Mod.Module :=
  r.modules.find? (·.header.modid == m)

/-- The variables a module binds at top level, in the order of its reduced body (its groups in
    Appendix A's order, the copies of a group in the order of emission, Choices, item 4). -/
def topVars (r : Mod.Reduced) (m : ModId) : Option (List Var) :=
  (module? r m).map fun md => (topDefs md.body).map (·.1)

/-- The right-hand side of a top-level variable. -/
def rhs (r : Mod.Reduced) (m : ModId) (x : Var) : Option Exp :=
  (module? r m).bind fun md => (topDefs md.body).lookup x

/-- The items of a module's header. -/
def headerItems (r : Mod.Reduced) (m : ModId) : Option Mod.ExpList :=
  (module? r m).map (·.header.exposing)

/-- The items of the written import of `n` by module `m` (after the default imports). -/
def importItems (r : Mod.Reduced) (m n : ModId) : Option (Option Mod.ExpList) :=
  (module? r m).bind fun md => ((md.imports.drop Mod.defaultImports.length).find? (·.modid == n)).map (·.exposing)

/-- A leaf of an expression: a special constant or an occurrence of a variable. -/
inductive Leaf where
  | c (sc : SCon)
  | v (lv : LongId)

mutual
/-- The leaves of an expression, left to right. -/
def leavesAt : AtExp → List Leaf
  | .scon sc => [.c sc]
  | .var lv => [.v lv]
  | .tuple e1 e2 e3 => leaves e1 ++ leaves e2 ++ leavesOpt e3
  | .record row => leavesRowOpt row
  | .update x row => .v ⟨none, x⟩ :: leavesRow row
  | .letE (.val vb) e => leavesVB vb ++ leaves e
  | .paren e => leaves e
  | _ => []
def leavesRow : ExpRow → List Leaf
  | .field _ e rest => leaves e ++ leavesRowOpt rest
def leavesRowOpt : Option ExpRow → List Leaf
  | none => []
  | some r => leavesRow r
def leaves : Exp → List Leaf
  | .atexp a => leavesAt a
  | .app e a => leaves e ++ leavesAt a
  | .lam _ e => leaves e
  | .caseE e m => leaves e ++ leavesMatch m
def leavesOpt : Option Exp → List Leaf
  | none => []
  | some e => leaves e
def leavesMatch : Match → List Leaf
  | .mk (.mk _ e) rest => leaves e ++ leavesMatchOpt rest
def leavesMatchOpt : Option Match → List Leaf
  | none => []
  | some m => leavesMatch m
def leavesVB : ValBind → List Leaf
  | .var _ e rest => leaves e ++ leavesVBOpt rest
  | .pat _ e => leaves e
def leavesVBOpt : Option ValBind → List Leaf
  | none => []
  | some vb => leavesVB vb
end

def Leaf.scon? : Leaf → Option SCon
  | .c sc => some sc
  | .v _ => none

def Leaf.var? : Leaf → Option LongId
  | .c _ => none
  | .v lv => some lv

/-- The special constants of a top-level definition's right-hand side, left to right. -/
def consts (r : Mod.Reduced) (m : ModId) (x : Var) : Option (List SCon) :=
  (rhs r m x).map fun e => (leaves e).filterMap Leaf.scon?

/-- The variables occurring in a top-level definition's right-hand side, left to right, with
    their qualifiers (`Basics.negate` of the derived negation included). -/
def occs (r : Mod.Reduced) (m : ModId) (x : Var) : Option (List LongId) :=
  (rhs r m x).map fun e => (leaves e).filterMap Leaf.var?

/-- A property of the result of the pipeline, when it succeeds. -/
def onOk {α : Type} (f : Mod.Reduced → α) : Except E2EError Mod.Reduced → Option α
  | .ok r => some (f r)
  | .error _ => none

/-- An unqualified long identifier. -/
abbrev lid (x : Var) : LongId := ⟨none, x⟩

/-- A qualified long identifier. -/
abbrev qlid (m : ModId) (x : Var) : LongId := ⟨some m, x⟩

/-! ## Instances recorded in an annotated program -/

/-- The occurrence of a variable whose instance is set by hand: `x` unqualified, the `k`th type
    of its instance replaced by `τ`. -/
structure Witness where
  x : Var
  k : Nat
  τ : Ty

def Witness.inst (w : Witness) (lv : LongId) (inst : List Ty) : List Ty :=
  if lv = ⟨none, w.x⟩ then inst.set w.k w.τ else inst

mutual
/-- An annotated phrase with the instance at every occurrence of `w.x` set by `w`. -/
def setAt (w : Witness) : AAtExp → AAtExp
  | .var lv inst τ => .var lv (w.inst lv inst) τ
  | .tuple e1 e2 e3 => .tuple (setExp w e1) (setExp w e2) (setExpOpt w e3)
  | .record row => .record (setRowOpt w row)
  | .update x inst τ row => .update x (w.inst ⟨none, x⟩ inst) τ (setRow w row)
  | .letE (.val VE vb) e => .letE (.val VE (setVB w vb)) (setExp w e)
  | .paren e => .paren (setExp w e)
  | a => a
def setRow (w : Witness) : AExpRow → AExpRow
  | .field l e rest => .field l (setExp w e) (setRowOpt w rest)
def setRowOpt (w : Witness) : Option AExpRow → Option AExpRow
  | none => none
  | some r => some (setRow w r)
def setExp (w : Witness) : AExp → AExp
  | .atexp a => .atexp (setAt w a)
  | .app e a => .app (setExp w e) (setAt w a)
  | .lam p e => .lam p (setExp w e)
  | .caseE e m => .caseE (setExp w e) (setMatch w m)
def setExpOpt (w : Witness) : Option AExp → Option AExp
  | none => none
  | some e => some (setExp w e)
def setMatch (w : Witness) : AMatch → AMatch
  | .mk (.mk p e) rest => .mk (.mk p (setExp w e)) (setMatchOpt w rest)
def setMatchOpt (w : Witness) : Option AMatch → Option AMatch
  | none => none
  | some m => some (setMatch w m)
def setVB (w : Witness) : AValBind → AValBind
  | .var x ann τ e rest => .var x ann τ (setExp w e) (setVBOpt w rest)
  | .pat p e => .pat p (setExp w e)
def setVBOpt (w : Witness) : Option AValBind → Option AValBind
  | none => none
  | some vb => some (setVB w vb)
end

mutual
/-- The instances recorded at the unqualified occurrences of `x`, left to right. -/
def instsAt (x : Var) : AAtExp → List (List Ty)
  | .var lv inst _ => if lv = ⟨none, x⟩ then [inst] else []
  | .tuple e1 e2 e3 => instsExp x e1 ++ instsExp x e2 ++ instsExpOpt x e3
  | .record row => instsRowOpt x row
  | .update y inst _ row => (if y = x then [inst] else []) ++ instsRow x row
  | .letE (.val _ vb) e => instsVB x vb ++ instsExp x e
  | .paren e => instsExp x e
  | _ => []
def instsRow (x : Var) : AExpRow → List (List Ty)
  | .field _ e rest => instsExp x e ++ instsRowOpt x rest
def instsRowOpt (x : Var) : Option AExpRow → List (List Ty)
  | none => []
  | some r => instsRow x r
def instsExp (x : Var) : AExp → List (List Ty)
  | .atexp a => instsAt x a
  | .app e a => instsExp x e ++ instsAt x a
  | .lam _ e => instsExp x e
  | .caseE e m => instsExp x e ++ instsMatch x m
def instsExpOpt (x : Var) : Option AExp → List (List Ty)
  | none => []
  | some e => instsExp x e
def instsMatch (x : Var) : AMatch → List (List Ty)
  | .mk (.mk _ e) rest => instsExp x e ++ instsMatchOpt x rest
def instsMatchOpt (x : Var) : Option AMatch → List (List Ty)
  | none => []
  | some m => instsMatch x m
def instsVB (x : Var) : AValBind → List (List Ty)
  | .var _ _ _ e rest => instsExp x e ++ instsVBOpt x rest
  | .pat _ e => instsExp x e
def instsVBOpt (x : Var) : Option AValBind → List (List Ty)
  | none => []
  | some vb => instsVB x vb
end

def setTop (w : Witness) : ATopDec → ATopDec
  | .value VE vb => .value VE (setVB w vb)
  | .typesSplit a1 a2 => .typesSplit (setTop w a1) (setTop w a2)
  | .seq a1 a2 => .seq (setTop w a1) (setTop w a2)
  | d => d

def instsTop (x : Var) : ATopDec → List (List Ty)
  | .value _ vb => instsVB x vb
  | .typesSplit a1 a2 => instsTop x a1 ++ instsTop x a2
  | .seq a1 a2 => instsTop x a1 ++ instsTop x a2
  | _ => []

/-- An annotated program with the instances at the occurrences of `w.x` set by `w`. -/
def setWitness (w : Witness) (a : AProgram) : AProgram :=
  a.map fun m => { m with body := m.body.map (setTop w) }

/-- The instances recorded at the unqualified occurrences of `x` in an annotated program. -/
def progInsts (x : Var) (a : AProgram) : List (List Ty) :=
  a.flatMap fun m => (m.body.map (instsTop x)).getD []

end SpecEx

open SpecEx

/-- The variables, constants and occurrences of a program read by a theorem below. -/
abbrev SpecEx.Vars := Option (List Var)
abbrev SpecEx.Consts := Option (List SCon)
abbrev SpecEx.Occs := Option (List LongId)

/- The views below are tuples of up to six options of lists; instance search for their decidable
   equality exceeds the default size bound. -/
set_option synthInstance.maxSize 4096

/-! ## A27: a free `number` is Float; a variable bound by an annotation is not defaulted -/

/-- `main = text (Debug.toString (2 ^ -1))`. -/
def s_a27_float_default : Src.SProgram := single "A27FloatDefault" [showMain (bin "^" (i 2) neg1)]

def a27FloatView (r : Mod.Reduced) : Consts := consts r "Main" "main"

/-- A27 (revised 2026-11-10; dynamic-core, "Defaulting of number"): the `number` of `2 ^ -1` is
    fixed by nothing, so it is Float, and both integer constants (`2`, and the `1` of the derived
    `Basics.negate 1`) are constants at Float. -/
theorem a27_float_default :
    onOk a27FloatView (endToEnd Btest s_a27_float_default) = some (some [.intF 2, .intF 1]) := by
  decide +kernel

/-- ```
    f : number -> number
    f x = let g y = y + x in g 1
    main = text (Debug.toString (f 2 // 1))
    ``` -/
def s_a27_annotation_bound : Src.SProgram := single "A27AnnotationBound"
  [val "f" (some (.fn (tv "number") (tv "number"))) [pv "x"]
     (.letE [.fn "g" none [pv "y"] (bin "+" (v "y") (v "x"))] (app (v "g") [i 1])),
   showMain (idiv (app (v "f") [i 2]) (i 1))]

def a27AnnView (r : Mod.Reduced) : Vars × Consts × Consts × Occs :=
  (topVars r "Main", consts r "Main" "f", consts r "Main" "f$Int", occs r "Main" "main")

/-- A27 (clarification of 2026-11-10), dynamic-core's `f`/`g` example: the `number` of `x` is bound
    by `f`'s annotation, not by the closure of `g`, and is not defaulted. So `g` is not copied, and
    its constant `1` follows the copy of `f` that encloses it: Float in `f`, Int in `f$Int`, the
    copy `main` uses. -/
theorem a27_annotation_bound :
    onOk a27AnnView (endToEnd Btest s_a27_annotation_bound) =
    some (some ["f", "f$Int", "main"], some [.intF 1], some [.int 1],
          some [lid "text", qlid "Debug" "toString", lid "f$Int"]) := by
  decide +kernel

/-! ## A87: the default copy is always made; a variable the declaration does not quantify -/

/-- ```
    check h = if h == 0 then h else Debug.todo "h"
    x = check (2 ^ -1)
    main = text (Debug.toString (x // 2))
    ``` -/
def s_a87_default_copy_made : Src.SProgram := single "A87DefaultCopyMade"
  [val "check" none [pv "h"] (.ifte [(bin "==" (v "h") (i 0), v "h")] (app (qv "Debug" "todo") [str "h"])),
   val "x" none [] (app (v "check") [.paren (bin "^" (i 2) neg1)]),
   showMain (idiv (v "x") (i 2))]

def a87CopyView (r : Mod.Reduced) : Vars × Occs × Consts × Occs × Consts × Occs :=
  (topVars r "Main", occs r "Main" "x", consts r "Main" "x", occs r "Main" "x$Int",
   consts r "Main" "x$Int", occs r "Main" "main")

/-- A87 (with A27 and A59), dynamic-core's `check`/`x` example: `main` uses `x` only at Int, yet
    the default copy `x` (at Float, where `2 ^ -1` is 0.5 and `check` reaches `Debug.todo`) is
    emitted beside `x$Int`; each copy of `x` uses the copy of `check` at its own assignment, and its
    constants are at its own type. -/
theorem a87_default_copy_made :
    onOk a87CopyView (endToEnd Btest s_a87_default_copy_made) =
    some (some ["check", "check$Int", "x", "x$Int", "main"],
          some [lid "check", qlid "Basics" "negate"], some [.intF 2, .intF 1],
          some [lid "check$Int", qlid "Basics" "negate"], some [.int 2, .int 1],
          some [lid "text", qlid "Debug" "toString", lid "x$Int"]) := by
  decide +kernel

/-- ```
    y = if 2 ^ -1 == 0 then 1 else 2
    main = text (Debug.toString (y // 1))
    ``` -/
def s_a87_vacuous_inner : Src.SProgram := single "A87VacuousInner"
  [val "y" none [] (.ifte [(bin "==" (bin "^" (i 2) neg1) (i 0), i 1)] (i 2)),
   showMain (idiv (v "y") (i 1))]

def a87InnerView (r : Mod.Reduced) : Vars × Consts × Consts :=
  (topVars r "Main", consts r "Main" "y", consts r "Main" "y$Int")

/-- A87, A43, A27 (dynamic-core, after the `check` example): the `number` of `2 ^ -1` (and of the
    `0` it is compared with) is not mentioned by the type of `y`, so it is not a variable of the
    declaration: no closure generalises it, and it is Float in every copy of `y`, `y$Int`
    included. Only the branches `1` and `2`, at `y`'s own variable, follow the copy. -/
theorem a87_vacuous_inner :
    onOk a87InnerView (endToEnd Btest s_a87_vacuous_inner) =
    some (some ["y", "y$Int", "main"], some [.intF 2, .intF 1, .intF 0, .intF 1, .intF 2],
          some [.intF 2, .intF 1, .intF 0, .int 1, .int 2]) := by
  decide +kernel

/-! ## A93: a `number` variable of a group that one binding's type does not mention -/

/-- A93's example:
    ```
    f n = if n <= 0 then 0 else if g 1 (n - 1) ^ -1 > 0 then 1 else 0
    g y k = if k <= 0 then y + 1 else let _ = f k in y + 1
    main = let _ = Debug.log "f 3" (f 3) in text "done"
    ``` -/
def s_a93_mutual : Src.SProgram := single "A93Mutual"
  [val "f" none [pv "n"] (.ifte [(bin "<=" (v "n") (i 0), i 0),
      (bin ">" (bin "^" (app (v "g") [i 1, .paren (bin "-" (v "n") (i 1))]) neg1) (i 0), i 1)] (i 0)),
   val "g" none [pv "y", pv "k"] (.ifte [(bin "<=" (v "k") (i 0), bin "+" (v "y") (i 1))]
      (.letE [.pat .wild (app (v "f") [v "k"])] (bin "+" (v "y") (i 1)))),
   val "main" none [] (.letE [.pat .wild (app (qv "Debug" "log") [str "f 3", .paren (app (v "f") [i 3])])]
      (app (v "text") [str "done"]))]

def a93View (r : Mod.Reduced) : Vars × Consts × Consts × Occs :=
  (topVars r "Main", consts r "Main" "f", consts r "Main" "g", occs r "Main" "main")

/-- What A93's example reduces to: one copy of the group `f`, `g`, its default copy (every
    constant at Float, the `1` of `g 1` inside `f` included, so that `f 3` is `1` as Elm 0.19.1
    prints), and `f 3` refers to `f`. -/
def a93Expected : Vars × Consts × Consts × Occs :=
  (some ["f", "g", "main"],
   some [.intF 0, .intF 0, .intF 1, .intF 1, .intF 1, .intF 0, .intF 1, .intF 0],
   some [.intF 0, .intF 1, .intF 1],
   some [qlid "Debug" "log", lid "f", lid "text"])

/-- A93 (option (b), with A27's Float default; dynamic-core, "Every binding of a declaration
    quantifies all the variables of class number of the declaration"): `f`'s type does not mention
    the `number` variable `b` of `g`'s `y`, but `f`'s scheme quantifies it; at `f 3` nothing fixes
    it, so it is Float, as are `n`'s and the result's, which `f 3` leaves free. There is no copy of
    the group at `b = Int`: `f` and `g` are emitted once, as their default copies. -/
theorem a93_mutual : onOk a93View (endToEnd Btest s_a93_mutual) = some a93Expected := by
  decide +kernel

/-- The group's number variables in canonical order (Choices, item 2) are those of `n`, of `f`'s
    result and of `g`'s `y` (`b`); `f`'s scheme binds them in that order (A93), so the third type of
    the instance recorded at `f 3` is the witness for `b`. Set by hand to Int. (The only other
    occurrence of `f`, `f k` inside its own group, records the empty instance.) -/
def a93Witness : Witness := ⟨"f", 2, tIntTy⟩

/-- The instances at `f` before and after the witness is set (their third types), whether the
    annotated program with the witness reduces as the one inference gives, and what it reduces to. -/
def a93WitnessView (a : AProgram) : List (Option Ty) × List (Option Ty) × Bool × Option (Vars × Consts × Consts × Occs) :=
  let a' := setWitness a93Witness a
  ((progInsts "f" a).map (·[2]?), (progInsts "f" a').map (·[2]?),
   decide ((reduceProgram Btest a').mapError E2EError.spec = (reduceProgram Btest a).mapError E2EError.spec),
   onOk a93View ((reduceProgram Btest a').mapError E2EError.spec))

/-- A93's example with the instance of the vacuous variable at `f 3` set to Int by hand in the
    annotated phrase that inference gives (where it is a free `number` variable, which the book's
    principal derivation does not determine): the reduced program is the same, `a93_mutual`'s. The
    witness is ignored, and the vacuous variable is Float at every occurrence (Choices, item 3;
    dynamic-core: "a variable that nothing at the occurrence fixes is Float"). -/
theorem a93_vacuous_witness :
    (inferProgram Btest (bareOf s_a93_mutual)).toOption.map a93WitnessView =
    some ([none, some (.var (.fresh 6 .num))], [none, some tIntTy], true, some a93Expected) := by
  decide +kernel

/-! ## The choices of the plan -/

/-- ```
    f : number -> Int -> Float
    f x n = if n <= 0 then 0.5 else f 1.5 (n - 1)
    main = text (Debug.toString (f (7 // 2) 3))
    ``` -/
def s_spec_polyrec : Src.SProgram := single "SpecPolyRec"
  [val "f" (some (.fn (tv "number") (.fn (tc "Int" []) (tc "Float" [])))) [pv "x", pv "n"]
     (.ifte [(bin "<=" (v "n") (i 0), fl 5 (-1))] (app (v "f") [f15, .paren (bin "-" (v "n") (i 1))])),
   showMain (app (v "f") [.paren (idiv (i 7) (i 2)), i 3])]

def polyrecView (r : Mod.Reduced) : Vars × Occs × Occs :=
  (topVars r "Main", occs r "Main" "f$Int", occs r "Main" "main")

/-- Polymorphic recursion through an annotation (dynamic-core: "even when a binding is used
    recursively at an instance other than its own"; Choices, items 4 and 5): `main` uses `f` at Int;
    inside `f$Int`, `f 1.5` is an occurrence at Float, so `f$Int` requests the default copy `f`.
    Both are emitted, `f` before `f$Int` (the order of emission, and Appendix A's regrouping puts
    `f`, which `f$Int` refers to, first). -/
theorem spec_polyrec :
    onOk polyrecView (endToEnd Btest s_spec_polyrec) =
    some (some ["f", "f$Int", "main"], some [lid "n", lid "f", lid "n"],
          some [lid "text", qlid "Debug" "toString", lid "f$Int"]) := by
  decide +kernel

/-- ```
    r : numberb -> numbera -> String
    r x y = Debug.toString (x + 1) ++ Debug.toString (y + 1)
    main = text (r (7 // 2) 1.5)
    ``` -/
def s_spec_two_vars_order : Src.SProgram := single "SpecTwoVarsOrder"
  [val "r" (some (.fn (tv "numberb") (.fn (tv "numbera") (tc "String" [])))) [pv "x", pv "y"]
     (bin "++" (app (qv "Debug" "toString") [.paren (bin "+" (v "x") (i 1))])
               (app (qv "Debug" "toString") [.paren (bin "+" (v "y") (i 1))])),
   val "main" none [] (app (v "text") [.paren (app (v "r") [.paren (idiv (i 7) (i 2)), f15])])]

def twoVarsView (r : Mod.Reduced) : Vars × Consts × Occs :=
  (topVars r "Main", consts r "Main" "r$Int$Float", occs r "Main" "main")

/-- The canonical order of a declaration's `number` variables is their first occurrence in the
    bindings' types (Choices, item 2), not the order of their names: `numberb` occurs before
    `numbera`, so the copy at `numberb = Int`, `numbera = Float` is `r$Int$Float`, where `x + 1`
    takes `1` at Int and `y + 1` at Float. -/
theorem spec_two_vars_order :
    onOk twoVarsView (endToEnd Btest s_spec_two_vars_order) =
    some (some ["r", "r$Int$Float", "main"], some [.int 1, .intF 1],
          some [lid "text", lid "r$Int$Float"]) := by
  decide +kernel

/-- ```
    import Basics exposing (abs)
    main = text (Debug.toString (abs (3 // -1) + abs (3 // -1) + Basics.abs 2 // 1))
    ``` -/
def s_spec_basis_abs : Src.SProgram := Src.canonOrder <| prog "spec" "SpecBasisAbs" [
  mdl (hdr false "Main" (.items [.var "main"]))
    [imp "Basics" none (some (.items [.var "abs"])), htmlText]
    [showMain (bin "+" (bin "+" (app (v "abs") [.paren (idiv (i 3) neg1)]) (app (v "abs") [.paren (idiv (i 3) neg1)]))
        (idiv (app (qv "Basics" "abs") [i 2]) (i 1)))]]

def absView (r : Mod.Reduced) : Occs × Option (Option Mod.ExpList) :=
  (occs r "Main" "main", importItems r "Main" "Basics")

/-- A value of the basis written in Elm (`abs`, Appendix D) is copied like a program's: its
    occurrences at Int, unqualified and qualified, refer to `abs$Int` and `Basics.abs$Int`, and the
    exposing item `abs` of the import stands for `abs, abs$Int` (sec:dynamic-modules-reduced). -/
theorem spec_basis_abs :
    onOk absView (endToEnd Btest s_spec_basis_abs) =
    some (some [lid "text", qlid "Debug" "toString", lid "abs$Int", qlid "Basics" "negate",
                lid "abs$Int", qlid "Basics" "negate", qlid "Basics" "abs$Int"],
          some (some (.items [.var "abs", .var "abs$Int"]))) := by
  decide +kernel

/-- ```
    module A exposing (f)
    f : number -> number
    f x = x + 1

    module Main exposing (main)
    import A exposing (f)
    main = text (Debug.toString (f 2 // 1))
    ``` -/
def s_spec_exposing : Src.SProgram := Src.canonOrder <| prog "spec" "SpecExposing" [
  mdl (hdr false "A" (.items [.var "f"])) []
    [val "f" (some (.fn (tv "number") (tv "number"))) [pv "x"] (bin "+" (v "x") (i 1))],
  mdl (hdr false "Main" (.items [.var "main"]))
    [imp "A" none (some (.items [.var "f"])), htmlText]
    [showMain (idiv (app (v "f") [i 2]) (i 1))]]

def exposingView (r : Mod.Reduced) : Option Mod.ExpList × Vars × Consts × Option (Option Mod.ExpList) × Occs :=
  (headerItems r "A", topVars r "A", consts r "A" "f$Int", importItems r "Main" "A", occs r "Main" "main")

/-- Copies across modules (sec:dynamic-modules-reduced): `A` makes `f$Int` because `Main` requests
    it (modules are specialised last to first); `A`'s header item `f` and `Main`'s import item `f`
    each stand for `f, f$Int`. -/
theorem spec_exposing :
    onOk exposingView (endToEnd Btest s_spec_exposing) =
    some (some (.items [.var "f", .var "f$Int"]), some ["f", "f$Int"], some [.int 1],
          some (some (.items [.var "f", .var "f$Int"])),
          some [lid "text", qlid "Debug" "toString", lid "f$Int"]) := by
  decide +kernel

/-- A concrete renaming: the permutation of the inference's fresh variables that swaps each
    `fresh n c` (n < 48, every class) with `fresh (n + 1000) c`, and each fresh row variable
    likewise. It is injective, keeps classes, fixes the named and the bound variables and every
    type name, so it is a renaming that `Renaming.WF Btest` admits. -/
def SpecEx.swapFresh : Renaming :=
  ⟨(List.range 48).flatMap (fun n => [Cls.any, Cls.num, Cls.comp, Cls.app, Cls.capp].flatMap fun c =>
      [(TyVar.fresh n c, TyVar.fresh (n + 1000) c), (TyVar.fresh (n + 1000) c, TyVar.fresh n c)]),
   (List.range 48).flatMap (fun n => [(RowVar.fresh n, RowVar.fresh (n + 1000)), (RowVar.fresh (n + 1000), RowVar.fresh n)]),
   []⟩

/-- Whether the program renamed reduces as the program does, and the instances recorded at the
    occurrences of `x` before and after the renaming. -/
def SpecEx.renameView (x : Var) (a : AProgram) : Bool × List (List Ty) × List (List Ty) :=
  (decide ((reduceProgram Btest (AProgram.rename swapFresh a)).mapError E2EError.spec =
           (reduceProgram Btest a).mapError E2EError.spec),
   progInsts x a, progInsts x (AProgram.rename swapFresh a))

/-- An instance of `reduceProgram_rename` (the invariance lemma: specialisation reads a type only
    through what a renaming preserves, Choices, item 2): the annotated program inference gives for
    `spec_exposing`, renamed by `swapFresh`, reduces to the same program. The renaming is not the
    identity on it: the instance of `text` in `main`, a fresh variable for `msg`, is renamed. -/
theorem spec_rename_invariant :
    (inferProgram Btest (bareOf s_spec_exposing)).toOption.map (renameView "text") =
    some (true, [[.var (.fresh 1 .any)]], [[.var (.fresh 1001 .any)]]) := by
  decide +kernel

/-- The same on A93's example, whose group's `number` variables are fresh ones (the instance at
    `f 3` is renamed), so that the canonical order of the variables and the copies are read
    through the renaming. -/
theorem spec_rename_invariant_a93 :
    (inferProgram Btest (bareOf s_a93_mutual)).toOption.map (renameView "f") =
    some (true, [[], [.var (.fresh 7 .num), .var (.fresh 5 .num), .var (.fresh 6 .num)]],
          [[], [.var (.fresh 1007 .num), .var (.fresh 1005 .num), .var (.fresh 1006 .num)]]) := by
  decide +kernel

/-- ```
    port module Main exposing (main)
    type alias P = { name : String, id : Int }
    port send : List P -> Cmd msg
    main = text "x"
    ``` -/
def s_spec_port_payload : Src.SProgram := Src.canonOrder <| prog "spec" "SpecPortPayload" [
  mdl (hdr true "Main" (.items [.var "main"])) [htmlText]
    [.alias "P" [] (.record [("name", tc "String" []), ("id", tc "Int" [])]),
     .port "send" (.fn (tc "List" [tc "P" []]) (tc "Cmd" [tv "msg"])),
     val "main" none [] (app (v "text") [str "x"])]]

def portView (r : Mod.Reduced) : Prog.PortEnv := r.ports

/-- A port keeps its direction and payload type as elaboration records them
    (sec:dynamic-modules-reduced): the alias is expanded and the record's fields are sorted by
    label. -/
theorem spec_port_payload :
    onOk portView (endToEnd Btest s_spec_port_payload) =
    some [("send", .out, .list (.record (.cons "id" .int (.cons "name" .string .nil))))] := by
  decide +kernel

/-- `{ init = \p -> ((), Cmd.none), update = \_ m -> (m, Cmd.none), subscriptions = \_ -> Sub.none }`. -/
def SpecEx.workerRec (p : Src.SPat) : Src.SExp :=
  .record [("init", .lam [p] (.tuple [.unit, qv "Cmd" "none"])),
           ("update", .lam [.wild, pv "m"] (.tuple [v "m", qv "Cmd" "none"])),
           ("subscriptions", .lam [.wild] (qv "Sub" "none"))]

/-- `main = text "v"`. -/
def s_main_view : Src.SProgram := single "SpecMainView" [val "main" none [] (app (v "text") [str "v"])]

/-- `main = Platform.worker { init = \() -> ..., ... }`: the flags type is `()` by the pattern. -/
def s_main_worker_unit : Src.SProgram := Src.canonOrder <| prog "spec" "SpecMainWorkerUnit" [
  mdl (hdr false "Main" (.items [.var "main"])) []
    [val "main" none [] (app (qv "Platform" "worker") [workerRec .unit])]]

/-- `main : Program Int () ()`, `main = Platform.worker { init = \_ -> ..., ... }`. -/
def s_main_worker_int : Src.SProgram := Src.canonOrder <| prog "spec" "SpecMainWorkerInt" [
  mdl (hdr false "Main" (.items [.var "main"])) []
    [val "main" (some (tc "Program" [tc "Int" [], .unit, .unit])) [] (app (qv "Platform" "worker") [workerRec .wild])]]

def kindView (r : Mod.Reduced) : Mod.ProgKind × Eff.PTy := (r.kind, r.flagsType)

/-- The kind of a program and its flags type, from the scheme of `main` (r:p-stat-main-view,
    r:p-stat-main-program; `mainKind`): a view, whose flags type is not read and is `()` (Choices,
    item 1; Translator changes, item 3); a worker whose flags type `()` its `init` fixes; a worker
    whose flags type `Int` its annotation fixes. -/
theorem spec_main_kinds :
    (onOk kindView (endToEnd Btest s_main_view), onOk kindView (endToEnd Btest s_main_worker_unit),
     onOk kindView (endToEnd Btest s_main_worker_int)) =
    (some (.view, .unit), some (.worker, .unit), some (.worker, .int)) := by
  decide +kernel

/-- `(1 // 1)`, an argument at Int. -/
def SpecEx.atInt : Src.SExp := .paren (idiv (i 1) (i 1))

/-- `(t a b c)`. -/
def SpecEx.tcall (a b c : Src.SExp) : Src.SExp := .paren (app (v "t") [a, b, c])

/-- ```
    t x y z = Debug.toString (x + 1) ++ Debug.toString (y + 1) ++ Debug.toString (z + 1)
    main = text ((t I I I) ++ (t I I F) ++ ... ++ (t F F F))
    ```
    with `I` = `(1 // 1)` and `F` = `1.5`: the eight assignments, Int first in `main`. -/
def s_spec_copy_bound : Src.SProgram := single "SpecCopyBound"
  [val "t" none [pv "x", pv "y", pv "z"]
     (bin "++" (app (qv "Debug" "toString") [.paren (bin "+" (v "x") (i 1))])
       (bin "++" (app (qv "Debug" "toString") [.paren (bin "+" (v "y") (i 1))])
                 (app (qv "Debug" "toString") [.paren (bin "+" (v "z") (i 1))]))),
   val "main" none [] (app (v "text") [.paren (
     bin "++" (tcall atInt atInt atInt) (bin "++" (tcall atInt atInt f15) (bin "++" (tcall atInt f15 atInt)
     (bin "++" (tcall atInt f15 f15) (bin "++" (tcall f15 atInt atInt) (bin "++" (tcall f15 atInt f15)
     (bin "++" (tcall f15 f15 atInt) (tcall f15 f15 f15))))))))])]

def copyBoundView (r : Mod.Reduced) : Vars × Consts × Consts :=
  (topVars r "Main", consts r "Main" "t$Float$Int$Int", consts r "Main" "t$Int$Float$Float")

/-- The bound of dynamic-core ("a declaration with k variables of class number has at most 2^k
    copies"), reached: three variables used at all eight assignments give eight copies, the default
    copy first and then the others in the lexicographic order of their assignments, Float before
    Int (Choices, item 4), whatever the order of the uses. -/
theorem spec_copy_bound :
    onOk copyBoundView (endToEnd Btest s_spec_copy_bound) =
    some (some ["t", "t$Float$Float$Int", "t$Float$Int$Float", "t$Float$Int$Int", "t$Int$Float$Float",
                "t$Int$Float$Int", "t$Int$Int$Float", "t$Int$Int$Int", "main"],
          some [.intF 1, .int 1, .int 1], some [.int 1, .intF 1, .intF 1]) := by
  decide +kernel

/-- `main = text (Debug.toString (let { x } = { x = 1 } in x // 2))`. -/
def s_spec_record_pattern_copy : Src.SProgram := single "SpecRecordPatternCopy"
  [showMain (.letE [.pat (.record ["x"]) (.record [("x", i 1)])] (idiv (v "x") (i 2)))]

/-- A record pattern binds the variables spelt as its labels, so a copy of a declaration by a
    record pattern cannot bind new variables (Issues, item 4): `x` is used at Int, its copy at Int
    is needed, and the specialisation refuses the program. -/
theorem spec_record_pattern_copy :
    endToEnd Btest s_spec_record_pattern_copy = .error (.spec (.recordPatternCopy "x")) := by
  decide +kernel

end StandardElm.Stat
