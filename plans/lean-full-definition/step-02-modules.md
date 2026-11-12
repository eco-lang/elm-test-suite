# Step 2: Chapter 7, ME0 and the effect values it needs

Part of [the plan](../lean-full-definition.md) (decisions D1 to D5). Conventions:
[conventions.md](conventions.md). Size: large. Needs: step 1. Status: **done** (2026-11-11; see "Progress" at the end).

## Goal

Encode Chapter 7 (`dynamic-modules.tex`) and the two dynamic program rules of Chapter 9
(`r:p-dyn-module`, `r:p-dyn-main`), with:

- the reduced module syntax, interfaces, module environments and bases, the merge of environments,
  the basic values `record(l1 ... ln)` and the port values, and the thunk translation of value
  groups as a Lean function with its freshness lemma;
- the 20 rules as relations, logged twins for the relations whose derivations can log (D4), an
  evaluator with soundness and completeness in the sense of D1;
- `ME0` for every module of the default imports, as literal Lean values with one derivation
  theorem per Elm text (D3), including `Ok`, `Err`, `logBase`, `never` and the effect values that
  `Cmd.none`, `Sub.none`, `batch`, `map` and `Platform.worker` build (D5);
- the test basis `Btest` (D2: the harness `Html` with `node#`, and a parameter for the library),
  the frame lemma and the `Btest` lemma, and the property of interfaces;
- theorems for rulings A25, A28, A38 and A82 on programs written by hand.

The let form of the tests is kept in this step (step 3 moves every test to module form); its
environment `E0` is now the one the default imports give by the rules, and it gains the 7 tests that
needed `Ok`, `Err`, `logBase` and `never`.

## Prerequisites

- Step 1 done: the oracle evaluator with `noValue_of_stuck`, uniqueness and completeness for
  `evExp`, `appVal`, `evDec`, `evValBind`; the logged Core relations; `Log`; `Val.toList?`; the
  twin check; the axioms script.
- The book:
  - `dynamic-modules.tex`: reduced syntax, lines 38 to 89; compound objects and the property of
    interfaces, lines 91 to 140; merge, lines 142 to 155; record constructors, lines 157 to 177;
    value groups and the thunk translation, lines 179 to 222; the rules, lines 224 to 498.
  - `programs.tex`: `r:p-dyn-module` (line 247), `r:p-dyn-main` (line 252), their comments (257 to
    272): a module is evaluated once, after the modules it imports; `main`'s value is taken from
    the module's own `VE`, so it need not be exposed; a top-level value with no value leaves the
    program without meaning.
  - `appendix-dynamic-basis.tex`: `E0` (lines 15 to 24); the value environments of `ME0`
    (Section `sec:appendix-dynamic-basis-env`, lines 171 to 361, Figures
    `fig:dynamic-basis-basics`, `fig:dynamic-basis-operators`, `fig:dynamic-basis-others`); the
    texts written in Elm and `E_K` (Section `sec:appendix-dynamic-basis-elm`, lines 363 to 551,
    Figure `fig:dynamic-basis-elm`); `Elm.Kernel.Basics.log` (Figure `fig:dynamic-basis-elem`,
    line 799); equality (Figure `fig:dynamic-basis-eq`, clause 4 for effect values); effect values
    (Section `sec:appendix-dynamic-basis-effects`, line 1182).
  - `syntax-modules.tex`: Figure `fig:default-imports` (lines 203 to 228).
  - `effects.tex`: CmdVal, SubVal and ProgVal (Figure `fig:effects-compound`, lines 110 to 196);
    `none` is `batch()` (lines 161 to 162 and 459 to 462); Figure `fig:effects-apply` (lines 419 to
    476) for `Cmd.batch`, `Cmd.map`, `Sub.batch`, `Sub.map`, `Platform.worker`.
  - `appendix-static-basis.tex`, lines 212 to 231: the hidden identifiers (`append` and the other
    operator variables, `JustOneMore`).

## Files

| File | Contents |
|------|----------|
| `StandardElmMech/Eff/PTy.lean` (new, namespace `StandardElm.Eff`) | `PTy`, the payload types; imported by `Objects.lean` |
| `StandardElmMech/Objects.lean` | new `BasVal` constructors; `Val.batch`, `Val.mapE`, `Val.prog`; `conNode`, `conJustOneMore`; `Env.plusEnv` |
| `StandardElmMech/Apply.lean` | APPLY on the new basic values; `eqSet` for effect values; `fLog` |
| `StandardElmMech/Show.lean` | `<internals>` for effect values |
| `StandardElmMech/InitialBasis.lean` | `VE_K` and `E_K` completed; the texts of `Basics`; `append` moved to the hidden variables |
| `StandardElmMech/Mod/Syntax.lean` | the reduced module syntax; `defaultImports`; `Module.withDefaults` |
| `StandardElmMech/Mod/Objects.lean` | `Interface`, `ConEnv`, `ModEnv`, `Basis`; `Interface.plus`; `Env.merge`; the thunk translation |
| `StandardElmMech/Mod/ME0.lean` | `ME0`, the Elm-text theorems, the harness, `Btest` |
| `StandardElmMech/Mod/Rules.lean` | the 20 rules, the auxiliary relations, `r:p-dyn-module`, `r:p-dyn-main` |
| `StandardElmMech/Mod/RulesL.lean` | logged twins, forget, lift |
| `StandardElmMech/Mod/Eval.lean` | the evaluators |
| `StandardElmMech/Mod/Sound.lean`, `Mod/Complete.lean` | soundness, completeness, monotonicity, agreement, uniqueness, `noMeaning_of_stuck` |
| `StandardElmMech/Mod/Properties.lean` | the property of interfaces, the frame lemmas, the `Btest` lemma |
| `StandardElmMech/Mod/Rulings.lean` | A25, A28, A38, A82 |
| `StandardElmMech/Basis.lean` | `E0` from the default imports |
| `StandardElmMech/Twins.lean` | four more pairs |

## Lean definitions

### Payload types (`Eff/PTy.lean`)

A port's basic value carries its payload type (`dynamic-modules.tex`, lines 173 to 177), and
`BasVal` precedes `Val`, so the type of payload types comes first. Step 4 gives it its meaning
(encoding and decoding); here it is only data.

```lean
namespace StandardElm.Eff

/-- The types τ with Port(τ) (static-modules.tex, Figure fig:static-modules-port). A record's
    fields are sorted by label, without duplicates (the translator writes them so), so that equal
    types are equal terms. -/
inductive PTy where
  | int | float | bool | string | bytes | unit | value          -- value: Json.Encode.Value
  | list (τ : PTy) | maybe (τ : PTy) | array (τ : PTy)
  | tuple2 (a b : PTy) | tuple3 (a b c : PTy)
  | record (fs : List (String × PTy))
  deriving Repr

instance : DecidableEq PTy    -- by deriving if Lean 4.35 derives it for this nested type, else by hand
```

### Values (`Objects.lean`)

```lean
inductive BasVal where
  | add | sub | ... | debugLog | debugTodo | debugToString      -- as today
  | kernelLog                                  -- Elm.Kernel.Basics.log, arity 1
  | record (ls : List Lab)                     -- record(l1 ... ln), n ≥ 1, arity n
  | outport (p : Var) (τ : Eff.PTy)            -- arity 1; APPLY in step 4
  | inport (p : Var) (τ : Eff.PTy)             -- arity 1; APPLY in step 4
  | cmdBatch | cmdMap | subBatch | subMap      -- Platform.Cmd.batch/map, Platform.Sub.batch/map
  | platformWorker                             -- Platform.worker, arity 1
  deriving Repr, DecidableEq, Inhabited

def BasVal.arity : BasVal → Nat      -- as today, and:
  -- kernelLog, outport, inport, cmdBatch, subBatch, platformWorker => 1
  -- cmdMap, subMap => 2;  record ls => ls.length

mutual
  inductive Val where
    | ...                                      -- as today
    | batch (cs : List Val)                    -- batch(c1 ... cn), in CmdVal and in SubVal
    | mapE (f : Val) (c : Val)                 -- map(v, c)
    | prog (r : List (String × Val))           -- prog r (ProgVal)
  inductive Env where
    | mk (QE : List (String × Env)) (VE : List (String × Val))
end

def conNode : Con := ⟨"node#", 1⟩                -- the harness's Html node (D2); no identifier spells it
def conJustOneMore : Con := ⟨"JustOneMore", 1⟩   -- the hidden constructor of Never

/-- Effect values of the kinds step 2 has: those `Cmd.batch` and `Cmd.map` accept. -/
def isCmdSub : Val → Bool
  | .batch _ | .mapE _ _ => true                 -- step 4 adds leaves
  | _ => false

/-- E + E': both components modified (dynamic-core.tex, projection and modification). -/
def Env.plusEnv (E E' : Env) : Env := .mk (fmPlus E.QE E'.QE) (fmPlus E.VE E'.VE)
```

The book's CmdVal and SubVal are distinct classes whose members are written alike (`effects.tex`,
lines 119 to 162); `batch()` is the same object in both (lines 161 to 162: "We write none for batch(), ...
in CmdVal and in SubVal"). So one constructor serves both, untagged, and `Cmd.none` and `Sub.none`
are the same value, as in the book. Leaves (`leaf(m, v)`), tasks, process identifiers, arrays and
boundary values are step 4's.

Structural functions on values gain these cases:

| Function | `batch cs` | `mapE f c` | `prog r` |
|----------|------------|------------|----------|
| `isFun` | `false` | `false` | `false` |
| `eqSet` (clause 4) | with `batch cs'`: if same length, `eqList cs cs'`, else `{False}` | with `mapE f' c'`: `(eqSet f f').conj (eqSet c c')` | with `prog r'`: as records (`recDomEq`, then `eqRec`) |
| `cmp` | none | none | none |
| `showVal` | `<internals>` | `<internals>` | `<internals>` |
| `normVal`, `recVE` | unchanged (fall-through) | unchanged | unchanged |

`<internals>` is what Elm/JS's `Debug.toString` prints for a value whose `$` tag is a number (effect
values); nothing in the suite prints one.

### APPLY (`Apply.lean`)

New constructors of `Apply`, one per line of the book's displays:

```lean
  -- fig:dynamic-basis-elem: Elm.Kernel.Basics.log; fLog follows the first applicable line
  | kernelLog_ (x : Float) : Apply .kernelLog [.sv (.float x)] (.sv (.float (fLog x)))
  -- dynamic-modules.tex, sec:dynamic-modules-record
  | record_ (ls : List Lab) (vs : List Val) :
      vs.length = ls.length → Apply (.record ls) vs (.record (ls.zip vs))
  -- effects.tex, fig:effects-apply
  | cmdBatch_ (v : Val) (cs : List Val) :
      v.toList? = some cs → cs.all isCmdSub = true → Apply .cmdBatch [v] (.batch cs)
  | subBatch_ (v : Val) (cs : List Val) :
      v.toList? = some cs → cs.all isCmdSub = true → Apply .subBatch [v] (.batch cs)
  | cmdMap_ (f c : Val) : isCmdSub c = true → Apply .cmdMap [f, c] (.mapE f c)
  | subMap_ (f c : Val) : isCmdSub c = true → Apply .subMap [f, c] (.mapE f c)
  | worker_ (r : Record) : Apply .platformWorker [.record r] (.prog r)

def fLog (x : Float) : Float :=
  if x.isNaN then fNaN else if x == 0 then -fInf else if x < 0 then fNaN
  else if x == fInf then fInf else x.log
```

`applySet` gains the matching cases, and `applySet_sound`, `applySet_complete` and
`applySet_length_le_two` are extended (each new case has exactly one member). `fLog` uses the C
library's `log` on its last line, which the kernel cannot reduce: a program that applies
`logBase` is `native` (the translator's `nativeValues` gains `logBase`, and `fromPolar`, `toPolar`,
which apply `cos`, `sin` and `atan2`). The port values have no APPLY case until step 4: see Risks.

### The texts of Basics and `E_K` (`InitialBasis.lean`)

`E_K = E0 + (QE_K, VE_K)` (`appendix-dynamic-basis.tex`, lines 436 to 460):

```lean
/-- The exposed basic values, constructors and floats of Basics (fig:dynamic-basis-basics, the
    lines not marked Elm). `append` is no longer here: it is the hidden variable of `++`. -/
def VE_BasicsExposed : ValEnv :=
  [ ("True", conv conTrue), ("False", conv conFalse),
    ("LT", conv conLT), ("EQ", conv conEQ), ("GT", conv conGT),
    ("toFloat", bas .toFloat), ("round", bas .round), ("floor", bas .floor),
    ("ceiling", bas .ceiling), ("truncate", bas .truncate),
    ("compare", bas .compare), ("min", bas .min), ("max", bas .max), ("clamp", bas .clamp),
    ("not", bas .not), ("xor", bas .xor), ("modBy", bas .modBy), ("remainderBy", bas .remainderBy),
    ("negate", bas .negate), ("sqrt", bas .sqrt),
    ("cos", bas .cos), ("sin", bas .sin), ("tan", bas .tan),
    ("acos", bas .acos), ("asin", bas .asin), ("atan", bas .atan), ("atan2", bas .atan2),
    ("isNaN", bas .isNaN), ("isInfinite", bas .isInfinite),
    ("e", .sv (.float fE)), ("pi", .sv (.float fPi)) ]

/-- The hidden variables of the operators (fig:dynamic-basis-operators), `append` included. -/
def hiddenOpVars : ValEnv := [ ("add", bas .add), ..., ("or", bas .or), ("append", bas .append) ]

def VE_K : ValEnv := VE_BasicsExposed ++ hiddenOpVars ++ [("JustOneMore", conv conJustOneMore)]

def E_K : Env :=
  E0base.plus [ ("Elm.Kernel.Basics", .mk [] [("log", bas .kernelLog)]),
                ("Basics", .mk [] VE_K) ] VE_K
```

`OTdyn "++"` now reads `fmLookup hiddenOpVars "append"`. The texts of Figure
`fig:dynamic-basis-elm` after the derived forms and number specialisation (each `.fn x ps e` stands
for `x = \p1 -> ... -> e`, `fI n` is an integer constant at Float):

```lean
def basicsTexts : List Def :=
  [ .fn "abs" [pv "n"] (ifte (ap (v "lt") [v "n", fI 0]) (.atexp (neg (vA "n"))) (v "n")),     -- default copy, at Float
    .fn "abs$Int" [pv "n"] (ifte (ap (v "lt") [v "n", i 0]) (.atexp (neg (vA "n"))) (v "n")),  -- the copy at Int
    .fn "logBase" [pv "base", pv "number"]
      (ap (v "fdiv") [ap (qv "Elm.Kernel.Basics" "log") [v "number"],
                      ap (qv "Elm.Kernel.Basics" "log") [v "base"]]),
    .fn "radians" [pv "angleInRadians"] (v "angleInRadians"),
    .fn "degrees" [pv "angleInDegrees"] (ap (v "fdiv") [ap (v "mul") [v "angleInDegrees", v "pi"], fI 180]),
    .fn "turns" [pv "angleInTurns"] (ap (v "mul") [ap (v "mul") [fI 2, v "pi"], v "angleInTurns"]),
    .fn "fromPolar" [ptup2 (P (pv "radius")) (P (pv "theta"))]
      (tup2 (ap (v "mul") [v "radius", ap (v "cos") [v "theta"]])
            (ap (v "mul") [v "radius", ap (v "sin") [v "theta"]])),
    .fn "toPolar" [ptup2 (P (pv "x")) (P (pv "y"))]
      (tup2 (ap (v "sqrt") [ap (v "add") [ap (v "mul") [v "x", v "x"], ap (v "mul") [v "y", v "y"]]])
            (ap (v "atan2") [v "y", v "x"])),
    .fn "identity" [pv "x"] (v "x"),
    .fn "always" [pv "a", pw] (v "a"),
    .fn "never" [PA (pcon "JustOneMore" [pv "nvr"])] (ap (v "never") [v "nvr"]) ]

/-- The hidden texts of the operators <<, >>, |>, <| (as today). -/
def opTexts : List Def := [composeL, composeR, apR, apL]   -- the four .fn of today's elmTexts

/-- The value of a text: by r:d-dec-nonrec the closure; for `never`, recursive, by r:d-dec-rec,
    Rec of it. -/
def elmTextValue : Def → Option (Var × Val)
  | .fn x (p :: ps) e =>
    let c := Val.closure p (lams ps e) E_K []
    if isRecursive [(x, c)] (.var x (lams (p :: ps) e) none) then some (x, (recVE [(x, c)]).head!.2)
    else some (x, c)
  | _ => none
```

### Module syntax (`Mod/Syntax.lean`)

The reduced syntax of `dynamic-modules.tex`, lines 38 to 89, one constructor per production of
Figures `fig:grammar-modules` and `fig:grammar-top-level-declarations` after the reductions:

```lean
namespace StandardElm.Mod
open StandardElm StandardElm.Eff

abbrev TyCon := String

inductive Dir where
  | out | inn
  deriving Repr, DecidableEq

inductive ExpItem where
  | var (x : Var)                 -- var (a value or a port; one item per copy, line 74)
  | op (o : Op)                   -- (opv)
  | tycon (t : TyCon)             -- tycon
  | opened (t : TyCon)            -- tycon(..)
  deriving Repr, DecidableEq

inductive ExpList where
  | all                           -- (..)
  | items (is : List ExpItem)     -- ( expitem1 , ... , expitemn ), n ≥ 1
  deriving Repr, DecidableEq

structure Header where
  isPort : Bool                   -- no dynamic content (r:dm-header's comment)
  modid : ModId
  exposing : ExpList

/-- import modid as modid' [exposing explist]; `import M` is read `import M as M` (line 80). -/
structure Import where
  modid : ModId
  qual : ModId
  exposing : Option ExpList

inductive ConBind where
  | mk (c : Con) (rest : Option ConBind)                -- con [| conbind], arity in Con

inductive DatBind where
  | mk (t : TyCon) (cb : ConBind) (rest : Option DatBind)

/-- tycon [= {lab1, ..., labn}]: `some ls` for a record alias, labels in the order written. -/
structure TypBind where
  tycon : TyCon
  labels : Option (List Lab)

inductive TopDec where
  | val (vb : List (Var × Exp))                 -- var1 = exp1 and ... and varn = expn, n ≥ 1
  | type (db : DatBind)
  | alias (tb : TypBind)
  | port (x : Var) (d : Dir) (τ : PTy)
  | seq (t1 t2 : TopDec)

/-- A module of the reduced syntax; `imports` are the default imports followed by the written
    ones (line 87). -/
structure Module where
  header : Header
  imports : List Import
  body : TopDec

/-- Figure fig:default-imports, in its order. -/
def defaultImports : List Import :=
  [ ⟨"Basics", "Basics", some .all⟩,
    ⟨"Debug", "Debug", none⟩,
    ⟨"List", "List", some (.items [.op "::"])⟩,
    ⟨"Maybe", "Maybe", some (.items [.opened "Maybe"])⟩,
    ⟨"Result", "Result", some (.items [.opened "Result"])⟩,
    ⟨"String", "String", some (.items [.tycon "String"])⟩,
    ⟨"Char", "Char", some (.items [.tycon "Char"])⟩,
    ⟨"Tuple", "Tuple", none⟩,
    ⟨"Platform", "Platform", some (.items [.tycon "Program"])⟩,
    ⟨"Platform.Cmd", "Cmd", some (.items [.tycon "Cmd"])⟩,
    ⟨"Platform.Sub", "Sub", some (.items [.tycon "Sub"])⟩ ]

def Module.withDefaults (h : Header) (written : List Import) (body : TopDec) : Module :=
  ⟨h, defaultImports ++ written, body⟩
```

A top-level value group is a list of pairs rather than a `ValBind`, because the rule needs its
variables and right-hand sides separately; `thunkGroup` makes the `ValBind` of the Core that the
rule's first premise evaluates. There is no empty `TopDec` (the grammar has none); a module with no
declaration does not occur.

### Objects of Chapter 7 (`Mod/Objects.lean`)

```lean
abbrev ConEnv := List (TyCon × ValEnv)

/-- (RA, CE, VE), Figure fig:dynamic-modules-compound. RA is a finite set, kept as a list. -/
structure Interface where
  RA : List TyCon
  CE : ConEnv
  VE : ValEnv

abbrev ModEnv := List (ModId × Interface)
abbrev Basis := ModEnv

def Interface.empty : Interface := ⟨[], [], []⟩
/-- "VE in Interface" = (∅, {}, VE). -/
def Interface.ofVE (VE : ValEnv) : Interface := ⟨[], [], VE⟩
/-- Modification component by component, the set by union. -/
def Interface.plus (I I' : Interface) : Interface := ⟨I.RA ++ I'.RA, fmPlus I.CE I'.CE, fmPlus I.VE I'.VE⟩
/-- I1 + ... + In. -/
def Interface.sum (Is : List Interface) : Interface := Is.foldl Interface.plus .empty

/-- The merge E1 ⊕ E2 of sec:dynamic-modules-merge: a qualifier common to both gets
    QE1(m) + QE2(m); otherwise whichever is defined; VE1 + VE2. -/
def mergeQE (q1 q2 : List (ModId × Env)) : List (ModId × Env) :=
  q2.map (fun (m, e2) => match fmLookup q1 m with
                         | some e1 => (m, e1.plusEnv e2)
                         | none => (m, e2))
  ++ q1.filter (fun (m, _) => !(q2.any (·.1 == m)))

def Env.merge (E1 E2 : Env) : Env := .mk (mergeQE E1.QE E2.QE) (fmPlus E1.VE E2.VE)

/-- The constructor of a record alias with labels ls (r:dm-typbind): record() is the empty record
    itself, which is not a basic value (line 167). -/
def recordCtor : List Lab → Val
  | [] => .record []
  | ls => .basApp (.record ls) []
```

The thunk translation (lines 191 to 216). `thunkVar x` is the new variable `x'`; it begins with `#`,
which no Elm identifier contains, so it "occurs nowhere in the program" whatever the program
(choice made: a spelling rather than a freshness search, as `[]`, `::`, `node#` and `arr#` are
spellings no identifier takes):

```lean
def thunkVar (x : Var) : Var := "#" ++ x
def forceExp (y : Var) : Exp := .app (.atexp (.var ⟨none, y⟩)) .unit      -- y ()

mutual
/-- ⟦·⟧ for the group whose variables are σ: free occurrences of x ∈ σ become (x' ()), and
    `{ x | exprow }` with x ∈ σ free becomes `let x = x' () in { x | ⟦exprow⟧ }`. Below a binder,
    σ loses the variables it binds, exactly as `fvExp` treats binders (Objects.lean). -/
def thunkAtExp (σ : List Var) : AtExp → AtExp
  | .var ⟨none, x⟩ => if σ.contains x then .paren (forceExp (thunkVar x)) else .var ⟨none, x⟩
  | .update x row =>
      if σ.contains x then
        .letE (.val (.var x (forceExp (thunkVar x)) none)) (.atexp (.update x (thunkExpRow σ row)))
      else .update x (thunkExpRow σ row)
  | .tuple e1 e2 e3 => .tuple (thunkExp σ e1) (thunkExp σ e2) (thunkExpOpt σ e3)
  | .record r => .record (thunkExpRowOpt σ r)
  | .letE (.val vb) e =>
      let σ' := removeAll σ (boundValBind vb)
      .letE (.val (thunkValBind σ' vb)) (thunkExp σ' e)
  | .paren e => .paren (thunkExp σ e)
  | a => a                                                  -- scon, qualified var, con, op, unit, nil
def thunkExp (σ : List Var) : Exp → Exp
  | .atexp a => .atexp (thunkAtExp σ a)
  | .app e a => .app (thunkExp σ e) (thunkAtExp σ a)
  | .lam p e => .lam p (thunkExp (removeAll σ (boundAtPat p)) e)
  | .caseE e m => .caseE (thunkExp σ e) (thunkMatch σ m)
def thunkMatch (σ : List Var) : Match → Match
  | .mk (.mk p e) rest => .mk (.mk p (thunkExp (removeAll σ (boundPat p)) e)) (thunkMatchOpt σ rest)
def thunkValBind (σ : List Var) : ValBind → ValBind      -- right-hand sides only
def thunkExpOpt, thunkExpRow, thunkExpRowOpt, thunkMatchOpt, thunkValBindOpt   -- structural
end

/-- ⟦valbind⟧ = x'1 = \_ -> ⟦exp1⟧ and ... and x'n = \_ -> ⟦expn⟧. -/
def thunkGroup (vb : List (Var × Exp)) : ValBind :=
  let σ := vb.map Prod.fst
  go σ vb
where
  go (σ : List Var) : List (Var × Exp) → ValBind
    | [] => .pat .wild (.atexp .unit)                        -- not reached: groups are non-empty
    | [(x, e)] => .var (thunkVar x) (.lam .wild (thunkExp σ e)) none
    | (x, e) :: rest => .var (thunkVar x) (.lam .wild (thunkExp σ e)) (some (go σ rest))
```

### `ME0`, the harness and `Btest` (`Mod/ME0.lean`)

The interfaces of the modules of the default imports, from Figures `fig:dynamic-basis-basics` and
`fig:dynamic-basis-others` and the constructor environments of lines 173 to 192. Every `RA` is
empty (the basis has no record alias).

| Module | `CE` | `VE` |
|--------|------|------|
| `Basics` | `Bool ↦ {True, False}`, `Order ↦ {LT, EQ, GT}`, `Never ↦ {}` | `VE_BasicsExposed` (31 bindings) and the values of the 11 exposed texts: `abs` (the copy at Float), `abs$Int`, `logBase`, `degrees`, `radians`, `turns`, `fromPolar`, `toPolar`, `identity`, `always`, `never` |
| `List` | `{}` | `{}` (in `ME0` for its type; library values are `Btest`'s parameter) |
| `Maybe` | `Maybe ↦ {Just, Nothing}` | `Just ↦ Just` (arity 1), `Nothing ↦ Nothing` (0) |
| `Result` | `Result ↦ {Ok, Err}` | `Ok ↦ Ok` (1), `Err ↦ Err` (1) |
| `String` | `{}` | `{}` |
| `Char` | `{}` | `toCode`, `fromCode` (basic values, 1) |
| `Tuple` | `{}` | `{}` |
| `Debug` | `{}` | `log` (2), `todo` (1), `toString` (1) |
| `Platform` | `{}` | `worker ↦ Platform.worker` (1) |
| `Platform.Cmd` | `{}` | `none ↦ batch()` (the value of its text), `batch ↦ Cmd.batch` (1), `map ↦ Cmd.map` (2) |
| `Platform.Sub` | `{}` | `none ↦ batch()`, `batch ↦ Sub.batch` (1), `map ↦ Sub.map` (2) |
| `Array`, `Bytes`, `Json.Encode`, `Json.Decode`, `VirtualDom`, `Html` | `{}` | `{}` (lines 332 to 339 of the appendix) |

`Task` and `Process` are not in `ME0` until step 4 (D3); the frame lemma covers programs that do
not import them.

```lean
def I_Basics : Interface :=
  ⟨[], [("Bool", [("True", conv conTrue), ("False", conv conFalse)]),
        ("Order", [("LT", conv conLT), ("EQ", conv conEQ), ("GT", conv conGT)]),
        ("Never", [])],
   VE_BasicsExposed ++ basicsTexts.filterMap elmTextValue⟩
def I_Maybe : Interface := ⟨[], [("Maybe", VE_Maybe)], VE_Maybe⟩
def I_Result : Interface := ⟨[], [("Result", VE_Result)], VE_Result⟩
  where VE_Result := [("Ok", conv conOk), ("Err", conv conErr)]
  -- conOk : Con := ⟨"Ok", 1⟩ and conErr : Con := ⟨"Err", 1⟩ are added to Objects.lean beside
  -- conJust; step 4 uses these names.
def I_Char : Interface := .ofVE [("toCode", bas .charToCode), ("fromCode", bas .charFromCode)]
def I_Debug : Interface := .ofVE [("log", bas .debugLog), ("todo", bas .debugTodo), ("toString", bas .debugToString)]
def I_Platform : Interface := .ofVE [("worker", bas .platformWorker)]

/-- The environments of the texts of Platform.Cmd and Platform.Sub (appendix-dynamic-basis.tex,
    lines 490 to 512): E0 with the module's own basic values unqualified. -/
def E_Cmd : Env := E0base.plus [] [("batch", bas .cmdBatch), ("map", bas .cmdMap)]
def E_Sub : Env := E0base.plus [] [("batch", bas .subBatch), ("map", bas .subMap)]
/-- `none = batch []`, the text of Platform/Cmd.elm and Platform/Sub.elm. -/
def noneText : Def := .fn "none" [] (ap (v "batch") [listE []])

def I_Cmd : Interface := .ofVE [("none", .batch []), ("batch", bas .cmdBatch), ("map", bas .cmdMap)]
def I_Sub : Interface := .ofVE [("none", .batch []), ("batch", bas .subBatch), ("map", bas .subMap)]

def ME0 : ModEnv :=
  [ ("Basics", I_Basics), ("List", .empty), ("Maybe", I_Maybe), ("Result", I_Result),
    ("String", .empty), ("Char", I_Char), ("Tuple", .empty), ("Debug", I_Debug),
    ("Platform", I_Platform), ("Platform.Cmd", I_Cmd), ("Platform.Sub", I_Sub),
    ("Array", .empty), ("Bytes", .empty), ("Json.Encode", .empty), ("Json.Decode", .empty),
    ("VirtualDom", .empty), ("Html", .empty) ]

/-- D2 (a): the harness Html. `text` is the constructor value node# of arity 1; no identifier
    spells node#, so it adds no kind of value and no APPLY case. -/
def I_HtmlHarness : Interface := .ofVE [("text", .con conNode [])]

/-- D2: the test basis. `lib` holds the core library's additions (core-library.md), empty until
    that plan's steps; they extend the interfaces of modules ME0 already has (List, Maybe, ...)
    component by component, and add modules it does not have. -/
def Btest (lib : ModEnv := []) : Basis :=
  lib.foldl (fun B (m, I) => match fmLookup B m with
                             | some I0 => fmPlus B [(m, I0.plus I)]
                             | none => fmPlus B [(m, I)])
            (fmPlus ME0 [("Html", I_HtmlHarness)])
```

### The rules (`Mod/Rules.lean`)

One relation per judgement form of Section `sec:dynamic-modules-rules` (lines 226 to 240), one
constructor per rule, named from its label; auxiliary relations for options and sequences
(constructors `opt_none`, `opt_some`, `seq_nil`, `seq_cons`). None is mutual with another except
`ConBind`/`ConBindOpt` and `DatBind`/`DatBindOpt`.

```lean
/-- Exposing Items: I ⊢ expitem ⇒ I' -/
inductive EvalExpItem : Interface → ExpItem → Interface → Prop where
  /-- r:dm-expitem-var -/
  | r_dm_expitem_var (I : Interface) (x : Var) (v : Val) :
      fmLookup I.VE x = some v → EvalExpItem I (.var x) (.ofVE [(x, v)])
  /-- r:dm-expitem-op -/
  | r_dm_expitem_op (I : Interface) (o : Op) : EvalExpItem I (.op o) .empty
  /-- r:dm-expitem-alias: con = tycon, so the key of the constructor is the tycon's spelling -/
  | r_dm_expitem_alias (I : Interface) (t : TyCon) (v : Val) :
      t ∈ I.RA → fmLookup I.VE t = some v → EvalExpItem I (.tycon t) ⟨[t], [], [(t, v)]⟩
  /-- r:dm-expitem-type -/
  | r_dm_expitem_type (I : Interface) (t : TyCon) (CE : ConEnv) :
      t ∉ I.RA → CE = (if (fmLookup I.CE t).isSome then [(t, [])] else []) →
      EvalExpItem I (.tycon t) ⟨[], CE, []⟩
  /-- r:dm-expitem-open -/
  | r_dm_expitem_open (I : Interface) (t : TyCon) (VE : ValEnv) :
      fmLookup I.CE t = some VE → EvalExpItem I (.opened t) ⟨[], [(t, VE)], VE⟩

inductive EvalExpItems : Interface → List ExpItem → List Interface → Prop where
  | seq_nil (I : Interface) : EvalExpItems I [] []
  | seq_cons (I : Interface) (it : ExpItem) (is : List ExpItem) (I1 : Interface) (Is : List Interface) :
      EvalExpItem I it I1 → EvalExpItems I is Is → EvalExpItems I (it :: is) (I1 :: Is)

/-- Exposing Lists: I ⊢ explist ⇒ I' -/
inductive EvalExpList : Interface → ExpList → Interface → Prop where
  /-- r:dm-explist-all -/
  | r_dm_explist_all (I : Interface) : EvalExpList I .all I
  /-- r:dm-explist-items -/
  | r_dm_explist_items (I : Interface) (is : List ExpItem) (Is : List Interface) :
      is ≠ [] → EvalExpItems I is Is → EvalExpList I (.items is) (Interface.sum Is)

inductive EvalExpListOpt : Interface → Option ExpList → Option Interface → Prop where
  | opt_none (I : Interface) : EvalExpListOpt I none none
  | opt_some (I : Interface) (el : ExpList) (I' : Interface) :
      EvalExpList I el I' → EvalExpListOpt I (some el) (some I')

/-- Headers: I ⊢ header ⇒ (modid, I') -/
inductive EvalHeader : Interface → Header → ModId → Interface → Prop where
  /-- r:dm-header -/
  | r_dm_header (I : Interface) (isPort : Bool) (m : ModId) (el : ExpList) (I' : Interface) :
      EvalExpList I el I' → EvalHeader I ⟨isPort, m, el⟩ m I'

/-- The unqualified part of an import: ∅ [+ VE of I']. -/
def unqualified : Option Interface → ValEnv
  | none => []
  | some I' => fmPlus [] I'.VE

/-- Imports: B ⊢ imports ⇒ E -/
inductive EvalImports : Basis → List Import → Env → Prop where
  /-- r:dm-imports-import -/
  | r_dm_imports_import (B : Basis) (m q : ModId) (el : Option ExpList) (rest : List Import)
      (I : Interface) (I' : Option Interface) (E : Env) :
      fmLookup B m = some I → EvalExpListOpt I el I' → EvalImports B rest E →
      EvalImports B (⟨m, q, el⟩ :: rest) (Env.merge (.mk [(q, .mk [] I.VE)] (unqualified I')) E)
  /-- r:dm-imports-empty -/
  | r_dm_imports_empty (B : Basis) : EvalImports B [] (.mk [] [])

mutual
/-- Constructor Bindings: ⊢ conbind ⇒ VE -/
inductive EvalConBind : ConBind → ValEnv → Prop where
  /-- r:dm-conbind -/
  | r_dm_conbind (c : Con) (rest : Option ConBind) (VE : ValEnv) :
      EvalConBindOpt rest VE → EvalConBind (.mk c rest) (fmPlus [(c.name, .con c [])] VE)
inductive EvalConBindOpt : Option ConBind → ValEnv → Prop where
  | opt_none : EvalConBindOpt none []
  | opt_some (cb : ConBind) (VE : ValEnv) : EvalConBind cb VE → EvalConBindOpt (some cb) VE
end

mutual
/-- Custom-type Bindings: ⊢ datbind ⇒ (CE, VE) -/
inductive EvalDatBind : DatBind → ConEnv → ValEnv → Prop where
  /-- r:dm-datbind -/
  | r_dm_datbind (t : TyCon) (cb : ConBind) (rest : Option DatBind) (VE : ValEnv) (CE' : ConEnv) (VE' : ValEnv) :
      EvalConBind cb VE → EvalDatBindOpt rest CE' VE' →
      EvalDatBind (.mk t cb rest) (fmPlus [(t, VE)] CE') (fmPlus VE VE')
inductive EvalDatBindOpt : Option DatBind → ConEnv → ValEnv → Prop where
  | opt_none : EvalDatBindOpt none [] []
  | opt_some (db : DatBind) (CE : ConEnv) (VE : ValEnv) : EvalDatBind db CE VE → EvalDatBindOpt (some db) CE VE
end

/-- Alias Bindings: ⊢ typbind ⇒ (RA, VE) -/
inductive EvalTypBind : TypBind → List TyCon → ValEnv → Prop where
  /-- r:dm-typbind -/
  | r_dm_typbind (t : TyCon) (ls : Option (List Lab)) :
      EvalTypBind ⟨t, ls⟩ (match ls with | none => [] | some _ => [t])
                          (match ls with | none => [] | some ls => [(t, recordCtor ls)])

/-- The premises E + Rec VE ⊢ x'1 () ⇒ v1 ... x'n () ⇒ vn of r:dm-topdec-val. -/
inductive EvalForces : Env → List Var → List Val → Prop where
  | seq_nil (E : Env) : EvalForces E [] []
  | seq_cons (E : Env) (y : Var) (ys : List Var) (v : Val) (vs : List Val) :
      EvalExp E (forceExp y) v → EvalForces E ys vs → EvalForces E (y :: ys) (v :: vs)

/-- Top-level Declarations: E ⊢ topdec ⇒ I -/
inductive EvalTopDec : Env → TopDec → Interface → Prop where
  /-- r:dm-topdec-val -/
  | r_dm_topdec_val (E : Env) (vb : List (Var × Exp)) (VE : ValEnv) (vs : List Val) :
      vb ≠ [] → EvalValBind E (thunkGroup vb) VE →
      EvalForces (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) vs →
      EvalTopDec E (.val vb) (.ofVE ((vb.map Prod.fst).zip vs))
  /-- r:dm-topdec-type -/
  | r_dm_topdec_type (E : Env) (db : DatBind) (CE : ConEnv) (VE : ValEnv) :
      EvalDatBind db CE VE → EvalTopDec E (.type db) ⟨[], CE, VE⟩
  /-- r:dm-topdec-alias -/
  | r_dm_topdec_alias (E : Env) (tb : TypBind) (RA : List TyCon) (VE : ValEnv) :
      EvalTypBind tb RA VE → EvalTopDec E (.alias tb) ⟨RA, [], VE⟩
  /-- r:dm-topdec-port-out -/
  | r_dm_topdec_port_out (E : Env) (x : Var) (τ : PTy) :
      EvalTopDec E (.port x .out τ) (.ofVE [(x, .basApp (.outport x τ) [])])
  /-- r:dm-topdec-port-in -/
  | r_dm_topdec_port_in (E : Env) (x : Var) (τ : PTy) :
      EvalTopDec E (.port x .inn τ) (.ofVE [(x, .basApp (.inport x τ) [])])
  /-- r:dm-topdec-seq -/
  | r_dm_topdec_seq (E : Env) (t1 t2 : TopDec) (RA1 : List TyCon) (CE1 : ConEnv) (VE1 : ValEnv) (I2 : Interface) :
      EvalTopDec E t1 ⟨RA1, CE1, VE1⟩ → EvalTopDec (E.plusVE VE1) t2 I2 →
      EvalTopDec E (.seq t1 t2) (Interface.plus ⟨RA1, CE1, VE1⟩ I2)

/-- Modules: B ⊢ module ⇒ B', VE -/
inductive EvalModule : Basis → Module → Basis → ValEnv → Prop where
  /-- r:dm-module: E0 is the environment binding [] and :: (E0base) -/
  | r_dm_module (B : Basis) (h : Header) (is : List Import) (td : TopDec) (E : Env)
      (I : Interface) (m : ModId) (I' : Interface) :
      EvalImports B is E → EvalTopDec (E0base.plusEnv E) td I → EvalHeader I h m I' →
      EvalModule B ⟨h, is, td⟩ [(m, I')] I.VE

/-- Evaluation of Programs: B ⊢DYN program ⇒ v (programs.tex) -/
inductive EvalProgram : Basis → List Module → Val → Prop where
  /-- r:p-dyn-module -/
  | r_p_dyn_module (B : Basis) (m : Module) (p : List Module) (B' : Basis) (VE : ValEnv) (v : Val) :
      EvalModule B m B' VE → EvalProgram (fmPlus B B') p v → p ≠ [] → EvalProgram B (m :: p) v
  /-- r:p-dyn-main -/
  | r_p_dyn_main (B : Basis) (m : Module) (B' : Basis) (VE : ValEnv) (v : Val) :
      EvalModule B m B' VE → fmLookup VE "main" = some v → EvalProgram B [m] v
```

That is 20 rules of Chapter 7 (`r_dm_module`, `r_dm_header`, `r_dm_imports_import`,
`r_dm_imports_empty`, `r_dm_explist_all`, `r_dm_explist_items`, `r_dm_expitem_var`,
`r_dm_expitem_op`, `r_dm_expitem_alias`, `r_dm_expitem_type`, `r_dm_expitem_open`,
`r_dm_topdec_val`, `r_dm_topdec_type`, `r_dm_topdec_alias`, `r_dm_topdec_port_out`,
`r_dm_topdec_port_in`, `r_dm_topdec_seq`, `r_dm_datbind`, `r_dm_conbind`, `r_dm_typbind`) and the two
of Chapter 9.

### Logged twins (`Mod/RulesL.lean`)

Only four of these relations have rules with a premise that can log: `EvalForces` (a Core
expression), `EvalTopDec` (through `EvalValBind` and `EvalForces`), `EvalModule` and
`EvalProgram`. The others (imports, exposing lists and items, headers, bindings of types) evaluate
no expression; their logs would always be empty, so they are used unchanged inside the logged
rules. (Choice made, and noted under "Issues with the plan".)

```lean
inductive EvalForcesL : Env → List Var → List Val → Log → Prop
  -- seq_nil_l: []; seq_cons_l: EvalExpL E (forceExp y) v l1 → EvalForcesL E ys vs l2 → ... (l1 ++ l2)
inductive EvalTopDecL : Env → TopDec → Interface → Log → Prop
  -- r_dm_topdec_val_l: EvalValBindL E (thunkGroup vb) VE l1 → EvalForcesL ... vs l2 → ... (l1 ++ l2)
  -- r_dm_topdec_type_l, _alias_l, _port_out_l, _port_in_l: []
  -- r_dm_topdec_seq_l: l1 ++ l2
inductive EvalModuleL : Basis → Module → Basis → ValEnv → Log → Prop
  -- r_dm_module_l: EvalImports (no log), EvalTopDecL ... l, EvalHeader (no log): l
inductive EvalProgramL : Basis → List Module → Val → Log → Prop
  -- r_p_dyn_module_l: EvalModuleL ... l1 → EvalProgramL ... l2 → ... (l1 ++ l2)
  -- r_p_dyn_main_l: EvalModuleL ... l → ... l
```

So the log of a program is the logs of its modules in program order; within a module, the logs of
its top-level declarations in the order of the derived form of Appendix A (custom types, aliases,
then ports and value groups in dependency order); within a group, the forcing of `x'1 () ... x'n ()`
in the order written. The first premise of `r_dm_topdec_val_l` always has the empty log (every
right-hand side of `thunkGroup vb` is a lambda), but it is kept, so that the twin check sees the
same premises.

`forget` and `lift`, as in step 1, by recursion on the derivation (these relations are not
mutual), using the Core's `forget`/`lift`:

```lean
theorem EvalProgramL.forget {B p v l} : EvalProgramL B p v l → EvalProgram B p v
theorem EvalProgram.lift {B p v} : EvalProgram B p v → ∃ l, EvalProgramL B p v l
-- and the same for EvalModule, EvalTopDec, EvalForces
```

### Evaluators (`Mod/Eval.lean`)

The parts without expressions are functions; the others thread the oracle and the log as step 1's
evaluator does, with the Core fuel `n` passed to every Core call (no fuel of their own: they recurse
on syntax).

```lean
def evExpItem (I : Interface) : ExpItem → Option Interface
  | .var x => (fmLookup I.VE x).map fun v => .ofVE [(x, v)]
  | .op _ => some .empty
  | .tycon t =>
      if t ∈ I.RA then (fmLookup I.VE t).map fun v => ⟨[t], [], [(t, v)]⟩
      else some ⟨[], if (fmLookup I.CE t).isSome then [(t, [])] else [], []⟩
  | .opened t => (fmLookup I.CE t).map fun VE => ⟨[], [(t, VE)], VE⟩
def evExpList (I : Interface) : ExpList → Option Interface
  | .all => some I
  | .items [] => none
  | .items is => (is.mapM (evExpItem I)).map Interface.sum
def evHeader (I : Interface) (h : Header) : Option (ModId × Interface)
def evImports (B : Basis) : List Import → Option Env
def evConBind : ConBind → ValEnv
def evDatBind : DatBind → ConEnv × ValEnv
def evTypBind : TypBind → List TyCon × ValEnv

def evForces (o : Oracle) (n : Nat) (E : Env) : List Var → Nat → Res (List Val)
def evTopDec (o : Oracle) (n : Nat) (E : Env) : TopDec → Nat → Res Interface
def evModule (o : Oracle) (n : Nat) (B : Basis) (m : Module) (k : Nat) : Res (Basis × ValEnv)
def evProgram (o : Oracle) (n : Nat) (B : Basis) : List Module → Nat → Res Val
```

`evTopDec` at `.val vb`: `stuck` if `vb.isEmpty`; else `evValBind o n E (thunkGroup vb) k`, then
`evForces o n (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) k1`, logs `l1 ++ l2`. `evModule`:
`evImports B m.imports` (`none` gives `stuck`), then `evTopDec o n (E0base.plusEnv E) m.body k`, then
`evHeader`. `evProgram`: `[]` is `stuck`; `[m]` looks up `"main"` in the module's `VE` (`none` gives
`stuck`); `m :: p` evaluates `p` in `fmPlus B B'`, logs `l1 ++ l2`.

## Theorems

### The thunk translation

```lean
def HashFree (σ : List Var) : Prop := ∀ x ∈ σ, x.front ≠ '#'

/-- No variable of the group remains free (feasibility review G1-6). -/
theorem thunk_closes {σ e} (h : HashFree σ) : ∀ x ∈ σ, x ∉ fvExp (thunkExp σ e)
/-- When no variable of the group is free, the translation is the identity (line 215). -/
theorem thunk_id {σ e} (h : ∀ x ∈ σ, x ∉ fvExp e) : thunkExp σ e = e
/-- The new variables are new: they begin with # (freshness lemma). -/
theorem thunkVar_fresh {e : Exp} {x : Var} (h : ∀ y ∈ allVarsExp e, y.front ≠ '#') :
    thunkVar x ∉ allVarsExp e
theorem thunkVar_injective : Function.Injective thunkVar
```

`allVarsExp` lists every unqualified variable of a phrase, bound or free (a new structural
function beside `fvExp`). Proofs by mutual structural induction on the phrase, following the clauses
of `thunkAtExp`; the record-update clause of `thunk_closes`: the result `let x = x' () in {x | ...}`
binds `x`, so `fvAtExp` removes it, and `x' ∉ σ` by `HashFree`. `thunkVar_fresh` is immediate from
`String.front ("#" ++ x) = '#'`.

### Elm texts of ME0 (D3)

One theorem per text, as `elmTexts_eval` today, named `me0_<Module>_<name>_eval`:

```lean
theorem me0_Basics_logBase_eval :
    EvalDec E_K (.val (.var "logBase" (lams [pv "base", pv "number"] logBaseBody) none))
      [("logBase", .closure (pv "base") (lams [pv "number"] logBaseBody) E_K [])]
theorem me0_Basics_never_eval :
    EvalDec E_K (.val (.var "never" (lams [neverPat] neverBody) none))
      (recVE [("never", .closure neverPat neverBody E_K [])])          -- by r:d-dec-rec
theorem me0_PlatformCmd_none_eval :
    EvalDec E_Cmd (.val (.var "none" (ap (v "batch") [listE []]) none)) [("none", .batch [])]
theorem me0_PlatformSub_none_eval :
    EvalDec E_Sub (.val (.var "none" (ap (v "batch") [listE []]) none)) [("none", .batch [])]
```

The list: `abs`, `abs$Int`, `logBase`, `radians`, `degrees`, `turns`, `fromPolar`, `toPolar`,
`identity`, `always`, `never` (`Basics`, in `E_K`); `composeL`, `composeR`, `apR`, `apL` (the hidden
texts of `OT_dyn`, in `E_K`); `none` (`Platform.Cmd`, in `E_Cmd`); `none` (`Platform.Sub`, in
`E_Sub`): 17 theorems. Method: the non-recursive ones by `elmText_derivation` (Theorems.lean) and
`decide +kernel` on `isRecursive`; `never` by `r_d_dec_rec` with `r_d_valbind_var` and
`r_d_exp_lambda`, `isRecursive` decided; the two `none` by `evDec_sound` on the evaluator's result
(`decide +kernel`, which runs `APPLY(Cmd.batch, [])`). Together with the literal `ME0` this means no
program theorem re-evaluates the basis.

```lean
/-- The values ME0 binds to the texts are the values of the texts. -/
theorem me0_texts : ∀ t ∈ basicsTexts, ∀ x v, elmTextValue t = some (x, v) → fmLookup I_Basics.VE x = some v
```

### Soundness, completeness and the D1 consequences (`Mod/Sound.lean`, `Mod/Complete.lean`)

```lean
theorem evExpItem_iff {I it I'} : evExpItem I it = some I' ↔ EvalExpItem I it I'
theorem evExpList_iff, evHeader_iff, evImports_iff     -- the same form
theorem evConBind_iff {cb VE} : evConBind cb = VE ↔ EvalConBind cb VE
theorem evDatBind_iff, evTypBind_iff

theorem evTopDec_sound_l {o n E td k I l k'} : evTopDec o n E td k = ⟨.value I, l, k'⟩ → EvalTopDecL E td I l
theorem evModule_sound_l {o n B m k B' VE l k'} :
    evModule o n B m k = ⟨.value (B', VE), l, k'⟩ → EvalModuleL B m B' VE l
theorem evProgram_sound_l {o n B p k v l k'} : evProgram o n B p k = ⟨.value v, l, k'⟩ → EvalProgramL B p v l
theorem evProgram_sound {o n B p k v} : (evProgram o n B p k).out = .value v → EvalProgram B p v

theorem evProgram_next_ge, evProgram_mono, evProgram_agree, evProgram_indep   -- as for evExp
theorem evProgram_complete_l {B p v l} (h : EvalProgramL B p v l) :
    ∃ L n, ∀ o k m, n ≤ m → Agrees o k L → evProgram o m B p k = ⟨.value v, l, k + L.length⟩
theorem evProgram_complete {B p v} (h : EvalProgram B p v) :
    ∃ L n, (evProgram (Oracle.ofList L) n B p 0).out = .value v

/-- A program on which the evaluator is stuck without reading a choice has no meaning. -/
theorem noMeaning_of_stuck {o n B p k l} (h : evProgram o n B p k = ⟨.stuck, l, k⟩) :
    ¬ ∃ v, EvalProgram B p v
theorem evProgram_unique_l {o n B p k v l} (h : evProgram o n B p k = ⟨.value v, l, k⟩) :
    ∀ v' l', EvalProgramL B p v' l' → v' = v ∧ l' = l
-- and the same seven for evModule and evTopDec
```

Methods: the `_iff` lemmas by induction on the syntax (lists of items and imports) and `cases` on
the relation. Soundness by induction on the syntax (`TopDec`, the list of modules), using step 1's
`evValBind_sound_l` and `evExp_sound_l`. Monotonicity, agreement and `next_ge` by the same induction
from step 1's lemmas (no fuel of their own). Completeness by induction on the derivation, combining
oracle lists by concatenation and fuels by `max`, as in step 1 (`Agrees.append`). The D1
consequences by step 1's argument, word for word.

### Properties (`Mod/Properties.lean`)

The property of interfaces (`dynamic-modules.tex`, lines 136 to 140):

```lean
def Interface.Good (I : Interface) : Prop :=
  (∀ t ∈ I.RA, (fmLookup I.VE t).isSome) ∧
  (∀ t VEt c v, fmLookup I.CE t = some VEt → fmLookup VEt c = some v → fmLookup I.VE c = some v)

/-- The names a top-level declaration binds in VE: group variables, ports, constructors, the
    constructors of record aliases. The restrictions of Section sec:syntax-modules-restrictions
    make them distinct. -/
def TopDec.boundNames : TopDec → List String

theorem ME0_good : ∀ md I, fmLookup (Btest []) md = some I → I.Good          -- decide +kernel
theorem EvalTopDec.good {E td I} : EvalTopDec E td I → td.boundNames.Nodup → I.Good
theorem EvalHeader.good {I h m I'} : EvalHeader I h m I' → I.Good → I'.Good
/-- The interfaces inferred by the rules have the property. -/
theorem EvalModule.good {B m B' VE} :
    EvalModule B m B' VE → m.body.boundNames.Nodup → ∀ md I, fmLookup B' md = some I → I.Good
```

Method: `EvalTopDec.good` by induction on the derivation; the `seq` case needs the domains of `VE1`
and `I2.VE` disjoint (from `Nodup` and a lemma `EvalTopDec.dom : EvalTopDec E td I → fmDom I.VE ⊆
td.boundNames`), so that `fmPlus` keeps each binding. `EvalHeader.good`: every binding of `I'.VE`
is a binding of `I.VE` (`r:dm-expitem-open` takes `VE = I.CE t`, whose bindings are `I.VE`'s by
`I.Good`), and every `CE` entry of `I'` is `{}` or an entry of `I.CE`.

The frame lemma (D3) and its program form:

```lean
def Module.imported (m : Module) : List ModId := m.imports.map (·.modid)

/-- A module's derivation reads the basis only at the modules it imports. -/
theorem EvalModuleL.frame {B B' m B'' VE l}
    (h : ∀ md ∈ m.imported, fmLookup B md = fmLookup B' md) :
    EvalModuleL B m B'' VE l ↔ EvalModuleL B' m B'' VE l

/-- The modules a program imports that it does not define before the importer. -/
def externalImports : List Module → List ModId

theorem EvalProgramL.frame {B B' p v l}
    (h : ∀ md ∈ externalImports p, fmLookup B md = fmLookup B' md) :
    EvalProgramL B p v l ↔ EvalProgramL B' p v l

/-- D3's soundness of a partial ME0: any basis that agrees with Btest on Btest's modules gives a
    program that imports nothing else from the basis the same meanings and logs. -/
theorem EvalProgramL.extend {B' p v l}
    (hB : ∀ md ∈ fmDom (Btest []), fmLookup B' md = fmLookup (Btest []) md)
    (hp : ∀ md ∈ externalImports p, md ∈ fmDom (Btest [])) :
    EvalProgramL (Btest []) p v l ↔ EvalProgramL B' p v l
```

Method: `EvalImports.frame` by induction on the imports (the only premise reading `B` is
`fmLookup B m`); `EvalModuleL.frame` by inversion of `r_dm_module_l`; the program form by induction
on `p`, generalising both bases (after a module, both become `fmPlus _ [(m, I')]`, which agree on the
module's id and elsewhere as before).

The `Btest` lemma (D2):

```lean
theorem Btest_agrees {lib md} (h1 : md ≠ "Html") (h2 : md ∉ fmDom lib) :
    fmLookup (Btest lib) md = fmLookup ME0 md
```

By induction on `lib` (each step changes only the binding of its own module) and `fmLookup_fmPlus`.

### Rulings (`Mod/Rulings.lean`)

Programs written by hand with `Module.withDefaults`. Each theorem's docstring carries `[params]`
and, where `Html.text` occurs, `[harness]`.

**A25** (a delayed self-reference forced during its own evaluation has no result;
`dynamic-modules.tex`, lines 432 to 436):

```lean
/-- x = let f _ = x in f () -/
def a25Body : Exp := .atexp (.letE (.val (.var "f" (.lam .wild (v "x")) none)) (.app (v "f") .unit))
def mA25 : Module := .withDefaults ⟨false, "A25", .all⟩ [] (.val [("x", a25Body)])

theorem a25_no_value (B : Basis) : ¬ ∃ B' VE, EvalModule B mA25 B' VE
theorem a25_no_meaning (B : Basis) (p : List Module) : ¬ ∃ v, EvalProgram B (mA25 :: p) v
```

Method. Inversion of `r_dm_module` and `r_dm_topdec_val`: any derivation contains
`EvalExp E' (forceExp "#x") v` with `E' = E1.plusVE (recVE VE1)` and, by inversion of
`EvalValBind` on `thunkGroup [("x", a25Body)]` (a lambda, `r_d_exp_lambda` only),
`VE1 = [("#x", .closure .wild (thunkExp ["x"] a25Body) E1 [])]`, for some `E1`. Then the loop lemma,
for every `E1`:

```lean
theorem a25_loop (E1 : Env) : ∀ o n k,
    (evExp o n (E1.plusVE (recVE [("#x", .closure .wild (thunkExp ["x"] a25Body) E1 [])]))
      (forceExp "#x") k).out = .outOfFuel
```

by strong induction on `n`: unfolding the evaluator a fixed number `c` of steps from fuel `n + c`
reaches `appVal o n' clo .unit k` with `clo` the same closure and `n' ≥ n` minus a constant, and
every lookup on the way finds its variable at the head of the environment (`fmPlus` puts the new
bindings first), so `E1` stays abstract; the fuels below `c` give `outOfFuel` by `simp`. A helper
does the induction once:

```lean
theorem diverges_of_reenters {α} (f : Nat → Res α) (c : Nat)
    (h : ∀ n, (f n).out = .outOfFuel → (f (n + c)).out = .outOfFuel)
    (h0 : ∀ n < c, (f n).out = .outOfFuel) : ∀ n, (f n).out = .outOfFuel
```

Then `noValue_iff` (step 1) gives `¬ ∃ v, EvalExp E' (forceExp "#x") v`. If the symbolic unfolding
proves awkward, the fallback is a direct proof by induction on the `EvalExp` derivation with a
motive that is `False` exactly for the judgements of the loop.

**A28 and A38** (a later import's names replace an earlier import's, a written import replaces a
default one; shared qualifiers merge; an ambiguous name that is not used is harmless;
`r:dm-imports-import`'s comment, lines 293 to 303):

```lean
/-- A module A with `type Maybe = Just Int Int | Nothing`, exposing (Maybe(..)). -/
def I_A28 : Interface := ⟨[], [("Maybe", VE_A28)], VE_A28⟩
  where VE_A28 := [("Just", .con ⟨"Just", 2⟩ []), ("Nothing", .con ⟨"Nothing", 0⟩ [])]

theorem a28_written_import_replaces_default :
    ∃ E, EvalImports (fmPlus (Btest []) [("A", I_A28)])
           (defaultImports ++ [⟨"A", "A", some (.items [.opened "Maybe"])⟩]) E ∧
         E.lookup ⟨none, "Just"⟩ = some (.con ⟨"Just", 2⟩ [])

/-- A binds a and x, B binds b and x. -/
def B38 : Basis := fmPlus (Btest []) [("A", .ofVE [("a", .int 1), ("x", .int 10)]),
                                      ("B", .ofVE [("b", .int 2), ("x", .int 20)])]

theorem a38_shared_qualifier_merge :
    ∃ E, EvalImports B38 [⟨"A", "Q", none⟩, ⟨"B", "Q", none⟩] E ∧
         E.lookup ⟨some "Q", "a"⟩ = some (.int 1) ∧ E.lookup ⟨some "Q", "b"⟩ = some (.int 2)
theorem a38_later_import_kept :
    ∃ E, EvalImports B38 [⟨"A", "A", some (.items [.var "x"])⟩, ⟨"B", "B", some (.items [.var "x"])⟩] E ∧
         E.lookup ⟨none, "x"⟩ = some (.int 20)
/-- Both imports expose x; the module never uses x; it has a meaning. -/
theorem a38_ambiguous_unused :
    EvalProgram B38 [.withDefaults ⟨false, "Main", .items [.var "main"]⟩
        [⟨"A", "A", some (.items [.var "x"])⟩, ⟨"B", "B", some (.items [.var "x"])⟩,
         ⟨"Html", "Html", some (.items [.var "text"])⟩]
        (.val [("main", .app (v "text") (strA "ok"))])]
      (.con conNode [.sv (.str "ok")])
```

Method: `evImports_iff` and `evProgram_sound` with `decide +kernel`.

**A82** (`main` need not be exposed; `programs.tex`, lines 262 to 266):

```lean
def mA82 : Module :=
  .withDefaults ⟨false, "Main", .items [.var "other"]⟩ [⟨"Html", "Html", some (.items [.var "text"])⟩]
    (.seq (.val [("other", i 1)]) (.val [("main", .app (v "text") (strA "ok"))]))

theorem a82_main_not_exposed : EvalProgram (Btest []) [mA82] (.con conNode [.sv (.str "ok")])
theorem a82_main_not_in_interface :
    ∀ B' VE, EvalModule (Btest []) mA82 B' VE → ∀ I, fmLookup B' "Main" = some I → fmLookup I.VE "main" = none
```

Method: the first by `evProgram_sound` and `decide +kernel`; the second by `evModule_unique_l`
(no choice is read) and `decide +kernel` on the computed basis.

## The let form in this step

`Basis.lean`'s hand-built `E0` is replaced by the environment the default imports give, so the let
form and the module form read one `ME0`:

```lean
def E_default : Env := (evImports ME0 defaultImports).getD (.mk [] [])
theorem E_default_eval : EvalImports ME0 defaultImports E_default := evImports_iff.mp (by decide +kernel)
def E0 : Env := E0base.plusEnv E_default
def E0with (cons : List (String × Nat)) : Env := E0.plusVE (cons.map fun (k, n) => (k, conv ⟨k, n⟩))
```

Differences from today's `E0`, none of which changes a value the tests compute: `append` is no
longer bound unqualified (it is hidden in the book; no test names it); `Ok`, `Err`, `logBase`,
`degrees`, `radians`, `turns`, `fromPolar`, `toPolar`, `never` are bound; the qualifiers `List`,
`Result`, `String`, `Tuple`, `Platform`, `Cmd`, `Sub` exist.

## Translator changes (the 7 tests)

In `definition/tools/src/Translate/`:

- `Convert.elm`: `basicsValues` gains `logBase`, `degrees`, `radians`, `turns`, `fromPolar`,
  `toPolar`, `never`; `resolveConstructor` resolves unqualified `Ok` and `Err` to `Global "" k`
  (the default import `Result(..)`); `qualifiedConstructor` accepts `Result.Ok`, `Result.Err`;
  `basicsValues` loses `append` (no test uses it; keeping it would name a hidden variable).
- `Basis.elm`: schemes `logBase : Float -> Float -> Float`, `degrees`, `radians`, `turns :
  Float -> Float`, `fromPolar : (Float, Float) -> (Float, Float)`, `toPolar` the same,
  `never : Never -> a`; constructors `Ok : a -> Result e a`, `Err : e -> Result e a`.
- `Infer.elm`: `builtin` gains `Result` (2 parameters) and `Never` (0).
- `Specialise.elm`: `nativeValues` gains `logBase`, `fromPolar`, `toPolar` (C library `log`,
  `cos`, `sin`, `atan2`).
- `ToLean.elm`: nothing new (`c "Ok"`, `v "logBase"` are already printable).

Tests to add to `TranslateTest.elm`: "Ok and Err are constructors of the default imports", "a
qualified Result.Err is accepted", "logBase makes the program native", "never is a value of Basics".

## Tests gained

In the let form, 7 tests, 13 checks: CaseFanOutShadowTest (3), CaseResultTest (3), ResultErrTest
(2), ResultOkTest (2), StandardA97NeverErrBranchTest (1), StandardA97SelfOnlyTypeTest (1),
LetNumberLogBaseTest (1, native: `logBase` and `round`).

## Acceptance

The commands of [conventions.md](conventions.md). Expected:

- `lake build`: no `sorry`, no new warning; `Twins.lean` checks 21 pairs (step 1's 17, and
  `EvalForces`, `EvalTopDec`, `EvalModule`, `EvalProgram`).
- `check-axioms`: 0 problems; the hand-written ruling theorems of `Mod/Rulings.lean` use no
  `native_decide`.
- Translator: `elm-spec tests: 939, translated: 498`; unit tests pass; `--check` up to date.
- `run-examples`: `Total: 1500 checks, 1500 agree, 0 diverge (0 known); K checks by decide +kernel,
  M by native_decide, in 498 program theorems.` with `K ≥ K1 + 12` and `M ≥ M1 + 1`, where `K1`,
  `M1` are step 1's figures; every `(program, label)` row of step 1's `example-run.json` unchanged.
- Memory budget as in the conventions.
- Site: `runner/mechanisation-data.js` links rule pages by the pattern `r_(d|dm|p)_<slug>`, and
  counts rules over `Rules.lean` and `Mod/Rules.lean` (48 + 22); the rule pages of the 20 `dm` rules
  and of `p-dyn-module`, `p-dyn-main` link to their constructors; link audit 0 problems. README
  Files table (rows for every new file) and "What the theorems say" (the rulings, `Btest` and the
  tag `[harness]`); report; preface count (498); plan status.

## Risks and fallbacks

- **APPLY on ports is missing until step 4.** The book's `APPLY(outport(p, τ), v)` and
  `APPLY(inport(p, τ), f)` are defined in Chapter 8; here they are empty, so the Lean relation has
  fewer derivations than the book's for a program that applies a port. Positive statements stay
  sound (every Lean derivation is a book derivation); a statement that something has no value is
  not made for a program that applies a port before step 4. No program of steps 2 and 3 applies one
  (the 15 port views never call their ports).
- **`DecidableEq` for `PTy` and `BasVal`.** If `deriving DecidableEq` fails on the nested `PTy`,
  write the instance by hand (structural recursion with a list helper).
- **Kernel cost of `ME0` in every let-form theorem.** `E0` is now computed by `evImports` inside each
  `decide`; the imports are 11 and the environments small, so this should be cheap. Fallback: make
  `E_default` a literal (generated once by `#eval` and pasted), with `E_default_eval` proving it.
- **A25's loop lemma** by symbolic unfolding may need many `simp` steps. Fallback named above.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

- **Payload types are needed before step 4.** The conventions put payload types in `Eff/` for step
  4, but the port values that `r:dm-topdec-port-out` and `r:dm-topdec-port-in` bind carry one, and
  `BasVal` comes before `Val`. This step defines the datatype `PTy` in `Eff/PTy.lean`; step 4 gives
  it its meaning.
- **Modules of `ME0` with empty interfaces.** D3 defers `Array`, `Bytes`, `Json.*` and
  `VirtualDom` to "when a step needs them". Step 3's 15 port views import `Array`, `Bytes`,
  `Json.Decode` and `Json.Encode`, whose dynamic interfaces are empty in the book; this step adds
  them now, exactly as the book has them. `Task` and `Process` stay for step 4.
- **D2's library part extends interfaces.** D2 says the core library's interfaces become entries of
  the test basis "as modules". `List`, `Maybe`, `Result`, `String`, `Char` and `Tuple` are already
  modules of `ME0`, so the library must extend their interfaces, not replace them (replacing
  `ME0(Maybe)` would lose `Just` and `Nothing`). `Btest` here merges component by component, and the
  `Btest` lemma excludes the modules the library touches.
- **What the `Btest` lemma compares with.** D2 asks for a lemma that `B_test` agrees with `B0` on
  every module but `Html` and the library's. Lean has no full `B0` until step 4 adds `Task` and
  `Process`, so the lemma compares with the encoded `ME0`, and `EvalProgramL.extend` (from the frame
  lemma) carries every result to any completion of `ME0` that agrees with it.
- **D4 and the relations that never log.** D4 says a logged relation is added "beside each relation
  of the book". For Chapter 7, the relations whose rules contain no logging premise (imports,
  exposing lists and items, headers, custom types, constructors, aliases) would have logs that are
  always empty; this specification gives twins only to `EvalForces`, `EvalTopDec`, `EvalModule` and
  `EvalProgram` and uses the others unchanged. Step 1 does give all 17 Core relations twins (the
  pattern relations' logs are always empty too) because the evaluator's single mutual block is
  simpler that way. The plan could state the rule: twins for every relation whose derivations can
  contain an application of `Debug.log`.
- **A finding about the existing encoding.** `Basis.lean`'s `E0` binds `append` unqualified, but
  `append` is a hidden variable of `Basics` (`appendix-static-basis.tex`, lines 215 to 221), bound in
  no interface. No test uses it; this step removes it.

## Progress

**2026-11-11, part 1 done: the values and the basis texts.**

- `Eff/PTy.lean`: the payload types, with the record fields as a mutual inductive `PFields`
  (Lean 4.35 does not derive `DecidableEq` for a type nested in `List (String × PTy)`).
- `Objects.lean`: the new basic values (`kernelLog`, `record ls`, `outport`, `inport`, `cmdBatch`,
  `cmdMap`, `subBatch`, `subMap`, `platformWorker`); `Val.batch`, `Val.mapE`, `Val.prog`;
  `conOk`, `conErr`, `conJustOneMore`, `conNode`; `Env.plusEnv`.
- `Apply.lean`: their APPLY lines and equality (clause 4); `fLog`. `applySet` is split into
  `applySetCore` (as before) and `applySetNew`, because adding the new lines to the one pattern
  match made the match compiler time out; soundness, completeness and the length bound are proved
  for both parts.
- `InitialBasis.lean`: `append` is hidden (only `++` reaches it), `E_K` has `JustOneMore` and the
  qualifier `Elm.Kernel.Basics`, and the texts of `logBase`, `degrees`, `radians`, `turns`,
  `fromPolar`, `toPolar` and the recursive `never` (its value by r:d-dec-rec).
- The let form's `E0` binds `Ok` and `Err` and the qualifier `Result`.
- Translator: `Ok`, `Err` and the new names of `Basics`, their schemes, `Result` as a built-in
  type, `logBase`, `fromPolar` and `toPolar` native, `append` no longer exposed.
- The 7 tests are translated: 498 of 939; 1,500 checks, all agreeing; 1,334 by the kernel, 166
  native, in 498 program theorems.

**2026-11-11, part 2 done: Chapter 7's rules, evaluator and soundness, ME0 and four rulings.**

- `Mod/Syntax.lean` (the reduced syntax, `defaultImports` as Figure `fig:default-imports` orders
  them: Basics, Debug, List exposing ((::)), Maybe, Result, String, Char, Tuple, Platform, Cmd,
  Sub), `Mod/Objects.lean` (interfaces, the merge, `recordCtor`, the thunk translation),
  `Mod/Rules.lean` (the 20 rules and `r:p-dyn-module`, `r:p-dyn-main`), `Mod/RulesL.lean` (the four
  logged twins, `forget`, `lift`), `Mod/Eval.lean`, `Mod/Sound.lean` (the functional parts and the
  evaluators sound), `Mod/ME0.lean` (ME0, the harness, `Btest`, `E_default` with
  `E_default_eval`), `Mod/Rulings.lean` (`a82_main_not_exposed`, `a38_shared_qualifier_merge`,
  `a38_later_import_kept`, `a38_ambiguous_unused`, `a28_written_import_replaces_default`).

**2026-11-11, part 3 done.** `Mod/Complete.lean`: the functional parts' converses (`eq_ev`),
`nostuck` for forcing, top-level declarations, modules and programs, `noMeaning_of_stuck`,
`evProgram_unique_l`, `evModule_unique_l`, completeness (`EvalProgramL.complete`,
`evProgram_complete`, `noMeaning_iff`). `Mod/Properties.lean`: `EvalImports.frame`,
`EvalModuleL.frame`, `EvalProgramL.frame`, `Btest_agrees`. The twin check covers the four logged
relations. `me0_PlatformCmd_none_eval`, `me0_PlatformSub_none_eval`, `never_eval`. The let form's
`E0` is `E0base.plusEnv E_default`, the environment the default imports give in ME0, and every value
is unchanged (1,500 checks agree). Build: largest process 3.1 GB, all together 9.1 GB.

**2026-11-11, part 4 done: the property of interfaces and A25. Step 2 is done.**

- `Mod/Good.lean`: `Interface.Good`, `TopDec.boundNames`, the domain lemmas (`EvalConBind.dom`,
  `EvalDatBind.dom`, `EvalTopDec.dom`), `EvalDatBind.good`, `EvalTopDec.good`, `EvalHeader.good`
  (through `Interface.PartOf`: every binding an exposing list gives is one of the module's, and the
  part has the property), `EvalModule.good`, and `ME0_good` for the test basis. Values have no
  decidable equality (closures), so `ME0_good` unfolds the concrete interfaces and closes each
  lookup by `rfl` rather than by `decide +kernel`.
- `Mod/A25.lean`: `a25_no_value` and `a25_no_meaning`. The symbolic unfolding of the
  specification's method works once `appVal` is kept out of the simp set and unfolded by hand, one
  closure at a time (`appVal_wild`): from fuel M + 14 the loop returns to forcing the thunk at
  M + 6 (`a25_step`), the fuels below 14 are computed, and `a25_loop` follows by strong induction;
  `evExp_complete` turns a derivation of the forcing into a run of the evaluator that would give a
  value. No `diverges_of_reenters` helper was needed.
- 1,673 theorems, 0 axiom problems.
