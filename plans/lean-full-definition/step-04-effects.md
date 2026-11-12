# Step 4: Chapter 8 (tasks, commands, subscriptions, ports)

Part of [the plan](../lean-full-definition.md); follows [conventions.md](conventions.md). Status:
specified 2026-11-11; nearly done (see Progress at the end).

Book references are to `definition/tex/effects.tex` (Chapter 8) unless another file is named.
`StandardElmMech/` is `definition/mechanisation/standard-elm-mech/StandardElmMech/`.

## Goal

Encode the whole of Chapter 8 in Lean, under decisions D4 (logged relations), D5 (effect values
as constructors of `Val`), D6 (exact numbers), D7 (canonical objects) and D8 (`enc` and `dec` as
structural functions, the book's relations beside them):

- the payload types (`sec:static-modules-ports`, Figure `fig:static-modules-port`) as an
  inductive `PTy`, and the boundary values `BVal` (`fig:effects-compound`), with JSON numbers as
  `Rat` and objects canonical;
- the effect values that step 2 has not added: tasks (`succeed`, `fail`, `andThen`, `onError`,
  `prim`), process identifiers, the managers including `in(p, τ)`, leaf commands and
  subscriptions, JSON values in `Val`, and the array and bytes constructor names `arr#` and
  `bin#`; with equality clauses 3 and 4 (`appendix-dynamic-basis.tex`, `fig:dynamic-basis-eq`),
  `showElm` and `isFun`;
- `APPLY` on the effect values (`fig:effects-apply`), `Task.command`, the port values
  `outport(p, τ)` and `inport(p, τ)` (`sec:effects-ports`), `Array.fromList` and
  `Array.toList` (`sec:appendix-dynamic-basis-arrays`);
- the `ME0` entries of `Task` and `Process`, with the elm/core 1.0.5 texts of `Task.map` to
  `Task.map5`, `Task.sequence` (with `List.foldr` and its helpers), `Task.mapError`,
  `Task.perform` and `Task.attempt` as literal values and one derivation theorem per text (D3);
- the 39 rules: task reduction (7), encoding (15), decoding (14), messages (3), each as one
  constructor, and their logged twins (D4);
- flattening (`sec:effects-commands`);
- the executable counterparts `stepTaskL`, `enc`, `dec`, `recvL`, with soundness and
  completeness;
- the book's properties: the property of task reduction (`sec:effects-tasks`), `Enc` and `Dec`
  are partial functions, and the round trip with A88's exceptions (`sec:effects-ports`);
- the rulings A74, A76, A88 and A92 as theorems.

This step gains no test: every test that needs Chapter 8 is a worker, which needs Chapter 9
(step 5). It is accepted by its theorems and by the unchanged counts of the existing checks.

## Prerequisites

This step needs step 2 (Chapter 7, `ME0`, the effect values of the default modules) and step 1
(the logged Core relations and the oracle evaluator). It does not need step 3. The interfaces
below are those of the step 1 and step 2 specifications of 2026-11-11, which were written in
parallel with this one. If their implementations rename something, the implementer renames
mechanically; if they change a shape, the shape below is the requirement and the difference is
recorded in the step report.

From step 1 (top-level `StandardElm` namespace, `Eval.lean`, `Complete.lean`, `Checks.lean`):

```lean
abbrev Log := List (String × Val)
abbrev Oracle := Nat → Bool                 -- the k-th choice of APPLY reads o k
def Oracle.const (b : Bool) : Oracle
inductive Outcome (α : Type) where | value (a : α) | stuck | outOfFuel
/-- outcome, log so far, index of the next unread choice -/
structure Res (α : Type) where
  out : Outcome α
  log : Log
  next : Nat

-- logged twins of the Core relations, constructors `<rule>_l`
inductive AppValL : Val → Val → Val → Log → Prop
inductive EvalExpL : Env → Exp → Val → Log → Prop
inductive EvalDecL : Env → Dec → ValEnv → Log → Prop
theorem AppValL.forget : AppValL f v w l → AppVal f v w
theorem AppVal.lift    : AppVal f v w → ∃ l, AppValL f v w l

-- the oracle evaluator (logged), fuel n, oracle index k
def appVal (o : Oracle) : Nat → Val → Val → Nat → Res Val
-- step 1's seven statements for appVal (as for evExp):
theorem appVal_sound      : (appVal o n f v k).out = .value w → AppValL f v w (appVal o n f v k).log
theorem appVal_mono       : (appVal o n f v k).out ≠ .outOfFuel → n ≤ m → appVal o m f v k = appVal o n f v k
theorem appVal_indep      : (appVal o n f v k).next = k → ∀ o', appVal o' n f v k = appVal o n f v k
def CompleteFor {α} (run : Oracle → Nat → Nat → Res α) (a : α) (l : Log) : Prop :=
  ∃ (L : List Bool) (n : Nat), ∀ o k m, n ≤ m → Agrees o k L → run o m k = ⟨.value a, l, k + L.length⟩
theorem AppValL.complete  : AppValL f v w l → CompleteFor (fun o m k => appVal o m f v k) w l
theorem appVal_unique_l   : appVal o n f v k = ⟨.value w, l, k⟩ → ∀ w' l', AppValL f v w' l' → w' = w ∧ l' = l
theorem appVal_noValue_of_stuck : appVal o n f v k = ⟨.stuck, l, k⟩ → ¬ ∃ w, AppVal f v w
```

(Step 1 states these for `evExp` and says "the same seven statements are stated for `appVal`,
`evDec` and `evValBind`"; the names above are those statements' names under step 1's naming
rule.)

From step 2 ([step-02-modules.md](step-02-modules.md); `StandardElm`, `StandardElm.Eff`,
`StandardElm.Mod`):

```lean
-- Eff/PTy.lean: the payload types, data only (step 4 gives their meaning)
inductive PTy where
  | int | float | bool | string | bytes | unit | value          -- value: Json.Encode.Value
  | list (τ : PTy) | maybe (τ : PTy) | array (τ : PTy)
  | tuple2 (a b : PTy) | tuple3 (a b c : PTy)
  | record (fs : List (String × PTy))                           -- fields sorted by label
instance : DecidableEq PTy
-- Objects.lean: BasVal constructors (APPLY of the port values is added here)
  | kernelLog | record (ls : List Lab)
  | outport (p : Var) (τ : Eff.PTy) | inport (p : Var) (τ : Eff.PTy)
  | cmdBatch | cmdMap | subBatch | subMap | platformWorker
-- Objects.lean: Val constructors (D5); commands and subscriptions share their forms
  | batch (cs : List Val)                    -- batch(c1 ... cn); none = batch []
  | mapE (f : Val) (c : Val)                 -- map(v, c)
  | prog (r : List (String × Val))           -- prog r
def isCmdSub : Val → Bool                    -- "step 4 adds leaves"
def Val.toList? : Val → Option (List Val)
-- Mod/Objects.lean and Mod/ME0.lean
structure Interface where RA : ... ; CE : ConEnv ; VE : ValEnv
def Interface.ofVE (VE : ValEnv) : Interface := ⟨[], [], VE⟩
def ME0 : ModEnv                              -- a literal (D3); Task and Process added here
def Btest (lib : ModEnv := []) : Basis        -- ME0 with the harness Html and the library (D2)
inductive Dir where | out | inn
```

`Ok` and `Err` are the constructor values `conv ⟨"Ok", 1⟩` and `conv ⟨"Err", 1⟩` of step 2's
`I_Result`; step 2 adds `conOk : Con := ⟨"Ok", 1⟩` and `conErr : Con := ⟨"Err", 1⟩` to
`Objects.lean` beside `conJust`, and this specification uses those names.

## Lean definitions

### Files

| File | Namespace | Contents | Imports |
|------|-----------|----------|---------|
| `Eff/PTy.lean` (step 2's, edited) | `StandardElm.Eff` | adds `PTy.Canon`, `PTy.normalise`, `tupleTy` | as step 2 |
| `Eff/Boundary.lean` | `StandardElm.Eff` | `BVal`, `BVal.Canon`, `BVal.mkObj`, `BVal.isJson`, `jnum`, `isDecimal`, `floatToRat?`, `ratToFloat` | `Objects` is *not* imported (BVal precedes Val) |
| `Objects.lean` (edited) | `StandardElm` | `Prim`, `Mgr`, the new `Val` constructors, `conArr`, `conBin`, `conPerform`, the new `BasVal` constructors | `Eff/PTy`, `Eff/Boundary` |
| `Eff/EncFn.lean` | `StandardElm.Eff` | `enc`, `dec` (structural, D8), `byteOf?` | `Objects` |
| `Apply.lean` (edited) | `StandardElm` | new `Apply` constructors, `applySet` cases, `eqSet` clauses 3 and 4, `isFun` | `Eff/EncFn` |
| `Show.lean` (edited) | `StandardElm` | `showVal` cases for the new constructors | `Objects` |
| `Eff/EncDec.lean` | `StandardElm.Eff` | the relations `Enc`, `Dec` (29 rules), the iff theorems | `Rules` (and step 1's logged file) |
| `Eff/Task.lean` | `StandardElm.Eff` | `Action`, `Out`, `TaskRed`, `TaskRedL`, `focus`, `plug`, `stepTaskL` | `Rules`, step 1's evaluator |
| `Eff/Flat.lean` | `StandardElm.Eff` | `flat`, `leafCore` | `Objects` |
| `Eff/Messages.lean` | `StandardElm.Eff` | `Input`, `Recv`, `RecvL`, `recvL` | `Eff/EncDec`, `Eff/Flat` |
| `Eff/TaskTexts.lean` | `StandardElm.Eff` | `E_List`, the `List` texts, `E_Task`, the `Task` texts, their values, derivation theorems, `ME0_Task`, `ME0_Process` | `Mod/` basis file of step 2, `Theorems` is not imported |
| `Eff/Properties.lean` | `StandardElm.Eff` | the task-reduction property, partiality, round trip, rulings | all of the above |
| `Eff/Examples.lean` | `StandardElm.Eff` | small kernel theorems used as acceptance checks | all of the above |

No file of this step imports `Lean` (conventions, memory). `StandardElmMech.lean` imports every new
file. `ME0` (step 2's literal in `Mod/ME0.lean`) gains the two entries `("Task", ME0_Task)` and
`("Process", ME0_Process)`; `Mod/ME0.lean` therefore imports `Eff/TaskTexts.lean` (which needs
only `Objects`, `Derived`, `InitialBasis` and step 1's relations, not `Mod/`), and step 2's
theorems about `ME0` (`ME0_good`, `Btest_agrees`, the frame lemma) are re-checked; `ME0_good` must
hold for the two new interfaces (decided by the kernel).

### Payload types (`Eff/PTy.lean`, additions)

Step 2's `PTy` has one constructor per clause of Figure `fig:static-modules-port`, with the two
tuple arities apart. Rule `r:e-enc-tuple` and rule `r:e-dec-tuple` cover both arities with an
option, as `Val.tuple` does; `tupleTy` gives the rule its type.

```lean
namespace StandardElm.Eff

/-- (τ1, τ2 [, τ3]) as a payload type. -/
def tupleTy (τ1 τ2 : PTy) : Option PTy → PTy
  | none => .tuple2 τ1 τ2
  | some τ3 => .tuple3 τ1 τ2 τ3

/-- Canonical: the fields of every record type strictly increasing by label (String `<`), so that
    a record type has one representation (D7; step 2 says the translator writes them so). -/
def PTy.Canon : PTy → Prop
/-- Sort the fields of every record type by label; `PTy.normalise_canon` proves the result
    canonical when the labels of each record are distinct. -/
def PTy.normalise : PTy → PTy
```

### Boundary values (`Eff/Boundary.lean`)

```lean
/-- BVal (fig:effects-compound): null, true, false, JSON numbers (D6: exact, as Rat), strings,
    byte sequences (A92), arrays and objects. Objects are canonical (D7): see `Canon`. -/
inductive BVal where
  | null | tru | fls
  | num   (q : Rat)
  | str   (s : String)
  | bytes (os : List Nat)                       -- each 0 ≤ o ≤ 255 (Canon)
  | arr   (js : List BVal)
  | obj   (kvs : List (String × BVal))          -- keys strictly increasing (Canon)
  deriving Repr, DecidableEq, Inhabited

/-- m × 10^e: the JSON number a numeral spells (effects.tex, sec:effects-simple). -/
def jnum (m e : Int) : Rat :=
  if 0 ≤ e then ((m * 10 ^ e.toNat : Int) : Rat) else mkRat m (10 ^ e.natAbs)

/-- q is a JSON number: its denominator has no prime factor other than 2 and 5. -/
def isDecimal (q : Rat) : Bool       -- strip factors 2 and 5 from q.den with fuel q.den, test = 1

/-- Canonical boundary values: numbers decimal, bytes below 256, object keys strictly
    increasing, recursively. -/
def BVal.Canon : BVal → Prop

/-- JVal: the boundary values in which no byte sequence occurs. -/
def BVal.isJson : BVal → Bool

/-- The normalising constructor of objects: sort by key; of duplicate keys the last wins
    (as a JSON parser reads them). The only way an object is built outside `enc`. -/
def BVal.mkObj (kvs : List (String × BVal)) : BVal :=
  .obj (dedupLastByKey kvs |>.mergeSort (fun a b => decide (a.1 ≤ b.1)))

/-- The exact value of a finite float, from its bits (as Show.lean's `floatParts`); `none` for
    NaN and the infinities. Both zeros give 0: a JSON number has no sign apart from its value
    (sec:effects-simple, A88). -/
def floatToRat? (x : Float) : Option Rat :=
  let b := x.toBits
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let fr := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0x7FF then none else
  let (m, e) : Nat × Int := if ex == 0 then (fr, -1074) else (fr + 2 ^ 52, (ex : Int) - 1075)
  let q : Rat := if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else mkRat m (2 ^ e.natAbs)
  some (if b >>> 63 == 1 then -q else q)

/-- float(j): the float nearest a decimal rational, rounded as the value of a floating-point
    constant is (Rules.lean `valof`: `Float.ofScientific`). For q = num/den with
    den = 2^a 5^b, k = max a b and M = |num| * (10^k / den): Float.ofScientific M true k,
    negated when num < 0. float(0) is +0. -/
def ratToFloat (q : Rat) : Float
```

Time and JSON numbers share `Rat` (D6). `floatToRat?` and `ratToFloat` reduce in the kernel:
`toBits` is already reduced by `showFloat`, and `Float.ofScientific` by `valof`, in today's kernel
theorems.

### Values (`Objects.lean`, edited)

```lean
/-- Prim: the primitives of Process (sec:effects-simple). Prim_plat is empty ([params]). -/
inductive Prim where | sleep | spawn | kill
  deriving Repr, DecidableEq, Inhabited
def Prim.arity : Prim → Nat := fun _ => 1
/-- Prim_plat and Mgr_plat, parameters of the platform; the empty platform ([params]). -/
def platPrims : List Prim := []

/-- Mgr (fig:effects-compound): the task manager, outgoing and incoming ports. Mgr_plat is
    empty ([params]), so it has no constructor here; rules that mention it get an unsatisfiable
    premise `m ∈ platMgrs` (step 5). -/
inductive Mgr where
  | task
  | out (p : String)
  | inn (p : String) (τ : Eff.PTy)
  deriving Repr, DecidableEq, Inhabited
def platMgrs : List Mgr := []

-- added to `inductive Val` (D5; the block stays Val and Env):
  | succeed (v : Val)                       -- succeed v
  | fail    (v : Val)                       -- fail v
  | andThen (f t : Val)                     -- andThen(v, tk)
  | onError (f t : Val)                     -- onError(v, tk)
  | prim    (π : Prim) (args : List Val)    -- prim(π, v1 ... vk), k = arity π
  | pid     (n : Nat)                       -- ProcId = Nat
  | leaf    (m : Mgr) (v : Val)             -- leaf(m, v); for m = out p, v is `.bv j`
  | bv      (j : Eff.BVal)                  -- a JSON value; or a boundary value in an out leaf

def conArr     : Con := ⟨"arr#", 1⟩          -- sec:appendix-dynamic-basis-arrays
def conBin     : Con := ⟨"bin#", 1⟩          -- sec:appendix-dynamic-basis-bytes
/-- The hidden constructor Perform of Task's MyCmd (sec:effects-apply). Spelt with a dot so that
    no constructor of a program has the same name (constructor names are compared by spelling). -/
def conPerform : Con := ⟨"Task.Perform", 1⟩

-- added to `inductive BasVal` (fig:effects-apply; sec:appendix-dynamic-basis-arrays;
-- sec:effects-ports); arity 1 except taskAndThen and taskOnError (2)
  | taskSucceed | taskFail | taskAndThen | taskOnError | taskCommand
  | processSleep | processSpawn | processKill
  | arrayFromList | arrayToList
  | outport (p : String) (τ : Eff.PTy)
  | inport  (p : String) (τ : Eff.PTy)

def Val.isOutcome : Val → Bool      -- succeed _ | fail _
-- step 2's isCmdSub gains `| .leaf _ _ => true` (its comment: "step 4 adds leaves"), so that
-- Cmd.batch and Cmd.map accept leaf commands
def Val.isTask    : Val → Bool      -- succeed, fail, andThen, onError, prim
```

Representation choices, each forced by D5 and the book's classes:

- `TaskVal`, `CmdVal` and `SubVal` are subsets of `Val`, not separate types. A task's component
  `t` in `andThen f t` is a `Val`; that it is a task is a property (`isTask`), true of every value
  `APPLY` builds, because the `Apply` constructors below require it of their arguments.
- A boundary value that is not a JSON value is not a value of the language (`sec:effects-compound`).
  `Val.bv j` holds a JSON value everywhere except as the argument of a leaf `leaf (.out p) (.bv j)`,
  where the book's CmdVal admits `Val ∪ BVal`. `Val.WF : Val → Prop` states this (every `.bv j`
  not directly under an `out` leaf has `j.isJson`), and `enc_value_json` below shows that
  `Json.Encode.Value` never carries a byte sequence.
- Process identifiers are natural numbers; the book's ProcId is any infinite set.

### Equality, order, printing (`Apply.lean`, `Show.lean`)

`eqSet` gains these cases, placed after clause 2 and before clause 5, in the book's clause order
(`fig:dynamic-basis-eq`):

```lean
-- clause 3: process identifiers and scalar boundary values
| .pid m, .pid n => BoolSet.just (m == n)
| .bv j, .bv j' => eqBV j j'
-- clause 4: effect values of the same form, same primitives, managers and port names
| .succeed a, .succeed b => eqSet a b
| .fail a, .fail b => eqSet a b
| .andThen f t, .andThen f' t' => (eqSet f f').conj (eqSet t t')
| .onError f t, .onError f' t' => (eqSet f f').conj (eqSet t t')
| .prim π vs, .prim π' vs' =>
    if π == π' && vs.length == vs'.length then eqList vs vs' else BoolSet.just false
| .leaf m v, .leaf m' v' => if m == m' then eqSet v v' else BoolSet.just false
```

```lean
/-- Clause 3 for null, true, false, numbers (equality of rationals, D6), strings and byte
    sequences; clause 4 for arrays (same length, componentwise) and objects (same key set,
    keywise). A boundary value holds no function, so the result is always a singleton. -/
def eqBV : BVal → BVal → BoolSet          -- mutual with eqBVList, eqBVObj (structural)
```

`cmp` gains nothing: no effect value is comparable (its last case gives `none`). `isFun` gains an
explicit `false` for each new constructor (effect values are not function values; the book's Fun
is closures, basic values and partial constructor values). `recVE` is unchanged.

`showVal` gains, as an implementation's `Debug.toString` (implementation-dependent, A62):

| Value | Printed |
|-------|---------|
| `succeed`, `fail`, `andThen`, `onError`, `prim`, `leaf`, `pid` (and step 2's `batch`, `mapE`, `prog`) | `<internals>` (as Elm/JS prints a kernel object) |
| `.con conArr [l]` | `Array.fromList ` followed by the list (as Elm/JS) |
| `.con conBin [l]` | `<k bytes>`, k the length of `l` (as Elm/JS prints a DataView) |
| `.bv j` | JSON text, keys in canonical order, numbers by `showFloat (ratToFloat q)` when not an integer and by the integer otherwise, byte sequences as `<k bytes>` |

`normVal` (Show.lean) is unchanged: it passes the new constructors through.

### APPLY (`Apply.lean`)

New constructors of `Apply`, one per row of Figure `fig:effects-apply`, and the port and array
values. Arguments the figure names by a class (`tk`, `pid`, `Perform tk`) are required to be of
that class, so that `APPLY` is not extended to values the figure leaves undefined.

```lean
  | taskSucceed_ (v : Val) : Apply .taskSucceed [v] (.succeed v)
  | taskFail_ (v : Val) : Apply .taskFail [v] (.fail v)
  | taskAndThen_ (f t : Val) : t.isTask = true → Apply .taskAndThen [f, t] (.andThen f t)
  | taskOnError_ (f t : Val) : t.isTask = true → Apply .taskOnError [f, t] (.onError f t)
  | taskCommand_ (t : Val) : t.isTask = true → Apply .taskCommand [.con conPerform [t]] (.leaf .task t)
  | processSleep_ (v : Val) : Apply .processSleep [v] (.prim .sleep [v])
  | processSpawn_ (t : Val) : t.isTask = true → Apply .processSpawn [t] (.prim .spawn [t])
  | processKill_ (n : Nat) : Apply .processKill [.pid n] (.prim .kill [.pid n])
  | arrayFromList_ (v : Val) : Apply .arrayFromList [v] (.con conArr [v])
  | arrayToList_ (v : Val) : Apply .arrayToList [.con conArr [v]] v
  /-- APPLY(outport(p, τ), v) = {leaf(out p, j) | Enc_τ(v) = j}, through `enc` (D8) -/
  | outport_ (p : String) (τ : Eff.PTy) (v : Val) (j : Eff.BVal) :
      Eff.enc τ v = some j → Apply (.outport p τ) [v] (.leaf (.out p) (.bv j))
  | inport_ (p : String) (τ : Eff.PTy) (f : Val) : Apply (.inport p τ) [f] (.leaf (.inn p τ) f)
```

`applySet` gains the matching cases (each a singleton list or `[]`), and `applySet_sound` its
cases; the tactic proof of `applySet_sound` is expected to cover them unchanged (the new cases have
the same shape as `debugLog`). `BasVal.arity` gains the arities above.

### `enc` and `dec` (`Eff/EncFn.lean`, D8)

Structural recursion on the payload type, mutual with the auxiliary over the nested
`List (String × PTy)` (the record fields). Lists use `vs.mapM (enc τ)` (the recursive call is on the
subterm `τ`). The two applications of the array rules are unfolded: `APPLY(Array.toList, arr# v)
= {v}` and `APPLY(Array.fromList, v) = {arr# v}` evaluate no closure.

```lean
mutual
def enc : PTy → Val → Option BVal
  | .int,    .sv (.int n)   => some (.num n)
  | .float,  .sv (.float x) => some ((floatToRat? x).elim .null .num)    -- r:e-enc-float(-null)
  | .bool,   .con c []      => if c == conTrue then some .tru else if c == conFalse then some .fls else none
  | .string, .sv (.str s)   => some (.str s)
  | .bytes,  .con c [l]     => if c == conBin then (l.toList? >>= (·.mapM byteOf?)).map .bytes else none
  | .unit,   .unit          => some .null
  | .maybe τ, .con c args   => if c == conNothing ∧ args = [] then some .null
                               else if c == conJust then (match args with | [v] => enc τ v | _ => none) else none
  | .list τ,  v             => v.toList? >>= (·.mapM (enc τ)) |>.map .arr
  | .array τ, .con c [l]    => if c == conArr then enc (.list τ) l else none   -- unfolds Array.toList
  | .tuple2 τ1 τ2, .tuple v1 v2 none =>
      do let j1 ← enc τ1 v1; let j2 ← enc τ2 v2; pure (.arr [j1, j2])
  | .tuple3 τ1 τ2 τ3, .tuple v1 v2 (some v3) =>
      do let j1 ← enc τ1 v1; let j2 ← enc τ2 v2; let j3 ← enc τ3 v3; pure (.arr [j1, j2, j3])
  | .record fs, .record r   => if recDomEq r (fs.map fun (l, _) => (l, Val.unit)) then
                                 (encFields fs r).map .obj else none
  | .value,  .bv j          => if j.isJson then some j else none
  | _, _ => none
def encFields : List (String × PTy) → List (String × Val) → Option (List (String × BVal))
  -- in the order of the type's fields; fmLookup r l for each label
end

mutual
def dec : PTy → BVal → Option Val
  | .int,    .num q => if q.den = 1 ∧ intMin ≤ q.num ∧ q.num ≤ intMax then some (.int q.num) else none
  | .float,  .num q => if isDecimal q then some (.sv (.float (ratToFloat q))) else none
  | .bool,   .tru => some (.bool true)
  | .bool,   .fls => some (.bool false)
  | .string, .str s => some (.sv (.str s))
  | .bytes,  .bytes os => if os.all (· < 256) then some (.con conBin [Val.ofList (os.map (Val.int ·))]) else none
  | .unit,   .null => some .unit
  | .maybe _, .null => some (.con conNothing [])
  | .maybe τ, j => (dec τ j).map fun v => .con conJust [v]     -- j ≠ null by the case above
  | .list τ,  .arr js => (js.mapM (dec τ)).map Val.ofList
  | .array τ, j => (dec (.list τ) j).map fun v => .con conArr [v] -- unfolds Array.fromList
  | .tuple2 τ1 τ2, .arr (j1 :: j2 :: _) =>                       -- further elements ignored
      do let v1 ← dec τ1 j1; let v2 ← dec τ2 j2; pure (.tuple v1 v2 none)
  | .tuple3 τ1 τ2 τ3, .arr (j1 :: j2 :: j3 :: _) =>
      do let v1 ← dec τ1 j1; let v2 ← dec τ2 j2; let v3 ← dec τ3 j3; pure (.tuple v1 v2 (some v3))
  | .record fs, .obj kvs => (decFields fs kvs).map .record       -- fields in the type's order
  | .value, j => if j.isJson then some (.bv j) else none
  | _, _ => none
def decFields : List (String × PTy) → List (String × BVal) → Option (List (String × Val))
end

def byteOf? : Val → Option Nat     -- .sv (.int n) with 0 ≤ n ≤ 255 ↦ n.toNat
```

The case `.maybe τ, j` after `.maybe _, .null` is the side condition `j ≠ null` of
`r:e-dec-just`. `dec` at a record gives the record with its fields in the type's (canonical,
sorted) order: the book's records are finite maps, and a fixed order makes `dec` a function on
representations (D7).

### The relations `Enc` and `Dec` (`Eff/EncDec.lean`)

One constructor per rule, named from the label (29 constructors); option and sequence
auxiliaries named `opt_*`, `seq_*`. The array rules have the book's `AppVal` premise, which is why
the relations come after `Rules.lean` (D8).

```lean
mutual
inductive Enc : PTy → Val → BVal → Prop where
  /-- r:e-enc-int -/        | r_e_enc_int (n : Int) : Enc .int (.sv (.int n)) (.num n)
  /-- r:e-enc-float -/      | r_e_enc_float (x : Float) (q : Rat) : floatToRat? x = some q → Enc .float (.sv (.float x)) (.num q)
  /-- r:e-enc-float-null -/ | r_e_enc_float_null (x : Float) : floatToRat? x = none → Enc .float (.sv (.float x)) .null
  /-- r:e-enc-true -/       | r_e_enc_true : Enc .bool (.bool true) .tru
  /-- r:e-enc-false -/      | r_e_enc_false : Enc .bool (.bool false) .fls
  /-- r:e-enc-string -/     | r_e_enc_string (s : String) : Enc .string (.sv (.str s)) (.str s)
  /-- r:e-enc-bytes -/      | r_e_enc_bytes (os : List Nat) : (∀ o ∈ os, o < 256) →
                                Enc .bytes (.con conBin [Val.ofList (os.map (Val.int ·))]) (.bytes os)
  /-- r:e-enc-unit -/       | r_e_enc_unit : Enc .unit .unit .null
  /-- r:e-enc-nothing -/    | r_e_enc_nothing (τ : PTy) : Enc (.maybe τ) (.con conNothing []) .null
  /-- r:e-enc-just -/       | r_e_enc_just (τ v j) : Enc τ v j → Enc (.maybe τ) (.con conJust [v]) j
  /-- r:e-enc-list -/       | r_e_enc_list (τ vs js) : EncSeq τ vs js → Enc (.list τ) (Val.ofList vs) (.arr js)
  /-- r:e-enc-array -/      | r_e_enc_array (τ v v' j) : AppVal (bas .arrayToList) v v' → Enc (.list τ) v' j →
                                Enc (.array τ) v j
  /-- r:e-enc-tuple -/      | r_e_enc_tuple (τ1 τ2 τ3 v1 v2 v3 j1 j2 j3) : Enc τ1 v1 j1 → Enc τ2 v2 j2 →
                                EncOpt τ3 v3 j3 → Enc (tupleTy τ1 τ2 τ3) (.tuple v1 v2 v3) (.arr ([j1, j2] ++ j3.toList))
  /-- r:e-enc-record: Dom r = Dom ρ, j an object with Dom j = Dom ρ, fieldwise -/
                            | r_e_enc_record (fs r kvs) : recDomEq r (fs.map fun (l, _) => (l, Val.unit)) = true →
                                EncFields fs r kvs → Enc (.record fs) (.record r) (.obj kvs)
  /-- r:e-enc-value -/      | r_e_enc_value (j : BVal) : j.isJson = true → Enc .value (.bv j) j
inductive EncSeq : PTy → List Val → List BVal → Prop         -- seq_nil, seq_cons
inductive EncOpt : Option PTy → Option Val → Option BVal → Prop  -- opt_none, opt_some
inductive EncFields : List (String × PTy) → List (String × Val) → List (String × BVal) → Prop
  -- seq_nil; seq_cons: fmLookup r l = some v → Enc τ v j → EncFields fs r kvs →
  --                    EncFields ((l, τ) :: fs) r ((l, j) :: kvs)
end
```

`Dec`, likewise, 14 constructors: `r_e_dec_int` (premise `q.den = 1 ∧ q.num ∈ IntRange`),
`r_e_dec_float` (premise `isDecimal q`; result `ratToFloat q`), `r_e_dec_true`, `r_e_dec_false`,
`r_e_dec_string`, `r_e_dec_bytes` (premise all bytes below 256), `r_e_dec_unit`,
`r_e_dec_nothing`, `r_e_dec_just` (premises `j ≠ .null`, `Dec τ j v`), `r_e_dec_list` (with
`DecSeq`), `r_e_dec_array` (premises `Dec (.list τ) j v`, `AppVal (bas .arrayFromList) v v'`),
`r_e_dec_tuple`:

```lean
  | r_e_dec_tuple (τ1 τ2 τ3 j1 j2 j3 rest v1 v2 v3) : Dec τ1 j1 v1 → Dec τ2 j2 v2 → DecOpt τ3 j3 v3 →
      (τ3 = none → j3 = none) →
      Dec (tupleTy τ1 τ2 τ3) (.arr (j1 :: j2 :: (j3.toList ++ rest))) (.tuple v1 v2 v3)
```

(`rest` is the book's `n ≥ k`: further elements are ignored), `r_e_dec_record` (premise
`DecFields fs kvs rs`, where `seq_cons` reads `fmLookup kvs l = some j`, `Dec τ j v`; conclusion
`Dec (.record fs) (.obj kvs) (.record rs)`: `Dom ρ ⊆ Dom j` because every label is looked up, and
`Dom r = Dom ρ` because `rs` has exactly the type's labels), and `r_e_dec_value` (premise
`j.isJson`).

No logged twins (plan, decision D4): the only applications in `Enc` and `Dec` are of
`Array.toList` and `Array.fromList`, which log nothing, so their logs would always be empty. A
rule of Chapters 8 or 9 that has an `Enc` or `Dec` premise contributes no log for it.

### Task reduction (`Eff/Task.lean`)

```lean
/-- An action π(v1 ... vk) → tk (fig:effects-compound): primitive, arguments, outcome. -/
structure Action where
  prim : Prim
  args : List Val
  outcome : Val

/-- tk ∈ Out(π, v1 ... vk) for the primitives of Process (sec:effects-tasks). The outcome of
    spawn is any process identifier; Chapter 9 chooses a fresh one. -/
inductive Out : Prim → List Val → Val → Prop where
  | sleep (v : Val) : Out .sleep [v] (.succeed .unit)
  | spawn (t : Val) (n : Nat) : Out .spawn [t] (.succeed (.pid n))
  | kill (n : Nat) : Out .kill [.pid n] (.succeed .unit)

/-- tk →[a] tk' (sec:effects-tasks); `none` is a silent reduction. -/
inductive TaskRed : Val → Option Action → Val → Prop where
  /-- r:e-task-andthen-succeed -/
  | r_e_task_andthen_succeed (v v' tk : Val) : AppVal v v' tk → TaskRed (.andThen v (.succeed v')) none tk
  /-- r:e-task-andthen-fail -/
  | r_e_task_andthen_fail (v v' : Val) : TaskRed (.andThen v (.fail v')) none (.fail v')
  /-- r:e-task-onerror-fail -/
  | r_e_task_onerror_fail (v v' tk : Val) : AppVal v v' tk → TaskRed (.onError v (.fail v')) none tk
  /-- r:e-task-onerror-succeed -/
  | r_e_task_onerror_succeed (v v' : Val) : TaskRed (.onError v (.succeed v')) none (.succeed v')
  /-- r:e-task-andthen-inner -/
  | r_e_task_andthen_inner (v tk tk' : Val) (a : Option Action) :
      TaskRed tk a tk' → TaskRed (.andThen v tk) a (.andThen v tk')
  /-- r:e-task-onerror-inner -/
  | r_e_task_onerror_inner (v tk tk' : Val) (a : Option Action) :
      TaskRed tk a tk' → TaskRed (.onError v tk) a (.onError v tk')
  /-- r:e-task-prim -/
  | r_e_task_prim (π : Prim) (vs : List Val) (tk : Val) :
      Out π vs tk → TaskRed (.prim π vs) (some ⟨π, vs, tk⟩) tk

inductive TaskRedL : Val → Option Action → Val → Log → Prop
  -- the same seven constructors with `_l`; andthen_succeed_l and onerror_fail_l take the log of
  -- their AppValL premise, the inner rules the log of their TaskRedL premise, the others []
```

The decomposition used by the property and by the evaluator:

```lean
inductive Frame where | andThen (f : Val) | onError (f : Val)
def plug : List Frame → Val → Val           -- innermost frame last: plug [F1, F2] t = F1[F2[t]]
/-- The redex of a task: descend through andThen/onError whose inner task is not an outcome.
    `none` for an outcome and for a value that is not a task. -/
def focus : Val → Option (List Frame × Val)
  | .andThen f t => if t.isOutcome then some ([], .andThen f t)
                    else (focus t).map fun (fs, r) => (.andThen f :: fs, r)
  | .onError f t => -- symmetric
  | .prim π vs   => some ([], .prim π vs)
  | _ => none
```

The executable step, with the outcome chooser for `r:e-task-prim` (the identifier given to a
spawned process):

```lean
/-- One reduction of tk, by the rules' only possible shape at `focus tk`. `fresh` is the
    process identifier a spawn returns. Stuck when tk is an outcome, not a task, a prim whose
    arguments Out does not accept, or when the application has no value; out of fuel when the
    application runs out. -/
def stepTaskL (o : Oracle) (n : Nat) (fresh : Nat) : Val → Nat → Res (Option Action × Val)
  | .andThen f (.succeed v), k => (appVal o n f v k).mapOut fun t => (none, t)
  | .andThen _ (.fail v),    k => ⟨.value (none, .fail v), [], k⟩
  | .onError f (.fail v),    k => (appVal o n f v k).mapOut fun t => (none, t)
  | .onError _ (.succeed v), k => ⟨.value (none, .succeed v), [], k⟩
  | .andThen f t,            k => (stepTaskL o n fresh t k).mapOut fun (a, t') => (a, .andThen f t')
  | .onError f t,            k => (stepTaskL o n fresh t k).mapOut fun (a, t') => (a, .onError f t')
  | .prim .sleep [v],        k => ⟨.value (some ⟨.sleep, [v], .succeed .unit⟩, .succeed .unit), [], k⟩
  | .prim .spawn [t],        k => ⟨.value (some ⟨.spawn, [t], .succeed (.pid fresh)⟩, .succeed (.pid fresh)), [], k⟩
  | .prim .kill [.pid p],    k => ⟨.value (some ⟨.kill, [.pid p], .succeed .unit⟩, .succeed .unit), [], k⟩
  | _,                       k => ⟨.stuck, [], k⟩
```

(`Res.mapOut` maps the value of a `Res` and keeps its log and index; defined here if step 1 has
no such helper. The recursion is structural on the task; the match arms are ordered so that an
`andThen` whose inner task is an outcome takes one of the first four arms.)

### Flattening (`Eff/Flat.lean`)

```lean
/-- Flat (sec:effects-commands) as a list in the order of the batches' components; the book's
    multiset is this list up to `List.Perm`. `none` for a value that is not a command or
    subscription. -/
def flat : Val → Option (List Val)          -- mutual with flatList (structural)
  | .batch cs => flatList cs
  | .mapE f c => (flat c).map (·.map (.mapE f))
  | .leaf m v => some [.leaf m v]
  | _ => none
/-- The manager and argument of a leaf command map(vn, ... map(v1, leaf(m, v)) ...). -/
def leafCore : Val → Option (Mgr × Val)
  | .mapE _ c => leafCore c
  | .leaf m v => some (m, v)
  | _ => none
```

### Messages (`Eff/Messages.lean`)

```lean
/-- The input of a leaf: a value (task leaves) or a port name with a boundary value. -/
inductive Input where | val (v : Val) | port (p : String) (j : BVal)

/-- c, receiving x, gives the message v (sec:effects-messages). -/
inductive Recv : Val → Input → Val → Prop where
  /-- r:e-msg-task -/
  | r_e_msg_task (tk v : Val) : Recv (.leaf .task tk) (.val v) v
  /-- r:e-msg-port -/
  | r_e_msg_port (p : String) (τ : PTy) (f : Val) (j : BVal) (v' v'' : Val) :
      Dec τ j v' → AppVal f v' v'' → Recv (.leaf (.inn p τ) f) (.port p j) v''
  /-- r:e-msg-map -/
  | r_e_msg_map (f c : Val) (x : Input) (v' v'' : Val) :
      Recv c x v' → AppVal f v' v'' → Recv (.mapE f c) x v''

inductive RecvL : Val → Input → Val → Log → Prop
  -- msg_task_l: []; msg_port_l: log of AppValL (Dec has no log, D4); msg_map_l: log of RecvL ++ log of AppValL

def recvL (o : Oracle) (n : Nat) : Val → Input → Nat → Res Val
/-- A structural test that no rule applies: an out leaf, a task leaf given a port input, a port
    leaf given a value or another port's input, or an undecodable boundary value. -/
def recvNone (c : Val) (x : Input) : Bool
```

### The texts of `Task` and `List.foldr` (`Eff/TaskTexts.lean`, D3)

The texts are those of elm/core 1.0.5 (`src/Task.elm`, `src/List.elm`), after the derived forms,
written with `Derived.lean`'s helpers (`ap`, `bin`, `v`, `qv`, `c`, `pv`, `caseOf`, `ifte`,
`i`). The implementer checks each against the files of elm/core 1.0.5 and cites the file and line
in the docstring.

```elm
-- List.elm (the further functions Task.sequence reaches)
foldl func acc list =
    case list of
        [] -> acc
        x :: xs -> foldl func (func x acc) xs

reverse list =
    foldl cons [] list

foldrHelper fn acc ctr ls =
    case ls of
        [] -> acc
        a :: r1 ->
            case r1 of
                [] -> fn a acc
                b :: r2 ->
                    case r2 of
                        [] -> fn a (fn b acc)
                        c :: r3 ->
                            case r3 of
                                [] -> fn a (fn b (fn c acc))
                                d :: r4 ->
                                    let
                                        res =
                                            if ctr > 500 then
                                                foldl fn acc (reverse r4)
                                            else
                                                foldrHelper fn acc (ctr + 1) r4
                                    in
                                    fn a (fn b (fn c (fn d res)))

foldr fn acc ls =
    foldrHelper fn acc 0 ls

-- Task.elm
map func taskA =
  taskA |> andThen (\a -> succeed (func a))
map2 func taskA taskB =
  taskA |> andThen (\a -> taskB |> andThen (\b -> succeed (func a b)))
map3 func taskA taskB taskC = ...   -- one more nesting per argument, to
map5 func taskA taskB taskC taskD taskE = ... succeed (func a b c d e)
sequence tasks =
  List.foldr (map2 (::)) (succeed []) tasks
mapError convert task =
  task |> onError (fail << convert)
perform toMessage task =
  command (Perform (map toMessage task))
attempt resultToMessage task =
  command (Perform (
    task
      |> andThen (succeed << resultToMessage << Ok)
      |> onError (succeed << resultToMessage << Err)
  ))
```

In Lean (excerpt; the others are written the same way):

```lean
def foldlText : Def := .fn "foldl" [pv "func", pv "acc", pv "list"]
  (caseOf (v "list")
    [ (P .nil, v "acc"),
      (.cons (P (pv "x")) (P (pv "xs")), ap (v "foldl") [v "func", ap (v "func") [v "x", v "acc"], v "xs"]) ])
def mapText : Def := .fn "map" [pv "func", pv "taskA"]
  (bin "|>" (v "taskA") (ap (v "andThen") [.lam (pv "a") (ap (v "succeed") [ap (v "func") [v "a"]])]))
def sequenceText : Def := .fn "sequence" [pv "tasks"]
  (ap (qv "List" "foldr") [ap (v "map2") [.atexp (.op "::")], ap (v "succeed") [.atexp .nil], v "tasks"])
def attemptText : Def := .fn "attempt" [pv "resultToMessage", pv "task"]
  (ap (v "command") [ap (c "Perform")
    [bin "|>" (bin "|>" (v "task")
                  (ap (v "andThen") [bin "<<" (v "succeed") (bin "<<" (v "resultToMessage") (c "Ok"))]))
              (ap (v "onError") [bin "<<" (v "succeed") (bin "<<" (v "resultToMessage") (c "Err"))])]])
```

`<<` is right-associative and `|>` left-associative (`fig:core-fixities`); the integer constants
of `foldrHelper` are at `Int` (number specialisation: `ctr : Int`).

The environments (`appendix-dynamic-basis.tex`, `sec:appendix-dynamic-basis-elm`: "the text of a
value of the module modid is evaluated in E_modid = E0 + (QE_modid, VE_modid)"; the values marked
"Elm" are taken in an order in which each text refers only to values already defined):

```lean
/-- E_List: the qualifier Basics (the derived form of `if` uses Basics.True and Basics.False),
    and `cons`, whose text `cons = Elm.Kernel.List.cons` is the list constructor `::`. -/
def E_List0 : Env := E0base.plus [("Basics", .mk [] VE_K)] [("cons", conv conCons)]
/-- The List texts in order foldl, reverse, foldrHelper, foldr; each in the environment of the
    earlier ones. foldl and foldrHelper are recursive: r:d-dec-rec, so their values are
    `recVE [(x, closure ...)]`. -/
def listTexts : List Def := [foldlText, reverseText, foldrHelperText, foldrText]
def listTextValues : ValEnv          -- by `textValues E_List0 listTexts` below
def foldrVal : Val := (fmLookup listTextValues "foldr").get!   -- stated as a literal closure

def VE_Task0 : ValEnv :=
  [ ("succeed", bas .taskSucceed), ("fail", bas .taskFail), ("andThen", bas .taskAndThen),
    ("onError", bas .taskOnError),
    ("command", bas .taskCommand), ("Perform", conv conPerform),   -- the two hidden names (A60, A85)
    ("Ok", conv conOk), ("Err", conv conErr), ("Just", conv conJust), ("Nothing", conv conNothing) ]
def QE_Task : List (String × Env) := [("List", .mk [] [("foldr", foldrVal)])]
def E_Task0 : Env := E0base.plus QE_Task VE_Task0
/-- map, map2, map3, map4, map5, sequence (after map2), mapError, perform (after map), attempt. -/
def taskTexts : List Def :=
  [mapText, map2Text, map3Text, map4Text, map5Text, sequenceText, mapErrorText, performText, attemptText]

/-- The values of texts taken in order: text k is evaluated in E + (the values of texts 0..k-1).
    A non-recursive text `x p ps = e` gives the closure (p, lams ps e, E_k, ∅) (r:d-dec-nonrec);
    a recursive one recVE of that binding (r:d-dec-rec). -/
def textValues (E : Env) : List Def → ValEnv

def VE_TaskIface : ValEnv :=
  [ ("succeed", bas .taskSucceed), ("fail", bas .taskFail),
    ("andThen", bas .taskAndThen), ("onError", bas .taskOnError) ] ++ textValues E_Task0 taskTexts
def VE_Process : ValEnv :=
  [ ("spawn", bas .processSpawn), ("sleep", bas .processSleep), ("kill", bas .processKill) ]

/-- The dynamic interfaces of ME0(Task) and ME0(Process): (∅, {}, VE)
    (sec:appendix-dynamic-basis-env, fig:dynamic-basis-others). -/
def ME0_Task : Mod.Interface := .ofVE VE_TaskIface
def ME0_Process : Mod.Interface := .ofVE VE_Process
```

The generated `textValues` are written out as literal closures in the file (as `VE_elm` is in
`InitialBasis.lean`), and a theorem checks that the literal equals `textValues ...` by
`decide +kernel` on a Boolean structural comparison, so that no test theorem recomputes them.

`List.foldr` here is a value of `QE_Task` only: `ME0(List)` has an empty dynamic interface
(`sec:appendix-dynamic-basis-env`). The core library's `List.foldr` in `B_test` (D2) is a
different Lean term with the same text; nothing identifies them.

## Theorems

Every theorem below is in `StandardElm.Eff` unless stated. Proof methods are named; "kernel"
means `decide +kernel`.

### Logged relations (D4)

```lean
theorem TaskRedL.forget : TaskRedL tk a tk' l → TaskRed tk a tk'
theorem TaskRed.lift    : TaskRed tk a tk' → ∃ l, TaskRedL tk a tk' l
theorem RecvL.forget    : RecvL c x v l → Recv c x v
theorem Recv.lift       : Recv c x v → ∃ l, RecvL c x v l
```

Method: induction on the derivation, using step 1's `AppValL.forget` and `AppVal.lift`; the
mutual auxiliaries by mutual structural recursion (checked feasible for Lean 4.35 by the
feasibility review, `scratchpad/exp/Forget.lean`). `encL_log_nil`: induction, and the lemma
`appValL_array_nil : AppValL (bas .arrayToList) v w l → l = []` (inversion: only
`r_d_app_basic_apply_l`, whose log is `[]` unless the basic value is `debugLog`), and its
`arrayFromList` twin.

The build's parity test (step 1's mechanism) gains the pairs `TaskRed/TaskRedL`,
`Recv/RecvL` (`Enc` and `Dec` have no logged twins, D4).

### `APPLY` lemmas

```lean
theorem appVal_arrayToList : AppVal (bas .arrayToList) v w ↔ ∃ l, v = .con conArr [l] ∧ w = l
theorem appVal_arrayFromList : AppVal (bas .arrayFromList) v w ↔ w = .con conArr [v]
theorem apply_effect_singleton (b : BasVal) (vs : List Val) (h : b.isEffect) :
    ∀ w w', Apply b vs w → Apply b vs w' → w = w'     -- "each set has exactly one member"
                                                      -- (sec:effects-apply), at most one here
```

Method: `cases` on `AppVal` (only `r_d_app_basic_apply` applies to a `basApp` of arity 1 with no
earlier argument) and on `Apply`. `BasVal.isEffect` is true of the twelve new constructors.

### `enc`, `dec` and the relations (D8)

```lean
theorem enc_iff (τ : PTy) (v : Val) (j : BVal) : Enc τ v j ↔ enc τ v = some j
theorem dec_iff (τ : PTy) (j : BVal) (v : Val) : Dec τ j v ↔ dec τ j = some v
```

Method: (→) mutual induction on the derivation, using `appVal_arrayToList`/`FromList` at the
array rules and `simp [enc]` elsewhere; (←) functional induction on `enc`/`dec` (or structural
induction on `τ` with an inner induction on the list), building each constructor. The auxiliaries
get their own iff lemmas (`encFields_iff`, `encSeq_iff`, ...).

### Partial functions (`sec:effects-ports`, first property)

```lean
theorem Enc.functional : Enc τ v j → Enc τ v j' → j = j'
theorem Dec.functional : Dec τ j v → Dec τ j v' → v = v'
```

Method: rewrite both with `enc_iff`/`dec_iff`; `Option.some.inj`.

The second sentence of the property ("every value that elaboration admits as a payload of type τ
has an encoding") needs the static semantics; it is stated here with a dynamic typing predicate,
and step 10 connects that predicate to elaboration:

```lean
/-- v is a value of the payload type τ: an Int value in IntRange at int, a float at float, ...,
    a record with exactly the type's labels, an `arr# l` with l a list of values of τ, a JSON
    value at value. -/
inductive HasPTy : PTy → Val → Prop
theorem enc_total : τ.Canon → HasPTy τ v → ∃ j, enc τ v = some j ∧ j.Canon
```

Method: induction on `HasPTy`. Canonicity of the object follows from `τ.Canon` (the object's keys
are the type's labels, in the type's order). This also gives the sentence after the property:
`APPLY(outport(p, τ), v)` has exactly one member for every `v` with `HasPTy τ v`.

### Round trip (`sec:effects-ports`, third sentence of the property; A88's exceptions)

```lean
/-- The exceptions of the property: v has no component that is NaN, an infinity or a negative
    zero (at a float position), and no component Just v' (at a Maybe τ position) whose argument
    encodes as null; and every Int component is in IntRange. -/
def NoExc : PTy → Val → Prop

/-- The one fact about Lean's Float the round trip needs: a finite float other than -0 is the
    nearest float to its own exact value. -/
def FloatRoundTrip : Prop := ∀ (x : Float) (q : Rat), ¬ isNegZero x → floatToRat? x = some q → ratToFloat q = x

theorem roundtrip (hF : FloatRoundTrip) (hτ : τ.Canon) (he : Enc τ v j) (hx : NoExc τ v) :
    Dec τ j (normVal v)
```

`normVal` (Show.lean) sorts the fields of every record; this is the book's `v''` (`v` with each
array replaced by `Array.fromList` of its elements, which in this representation is `v` itself,
since `Array.fromList (Array.toList (arr# l)) = arr# l`), with the record fields in the canonical
order in which `dec` builds them. Method: induction on `Enc` (via `enc_iff`); the float case is
`hF`; the Maybe case uses the `NoExc` hypothesis to exclude `j = .null` under `Just`; the record
case uses `hτ` (the type's order is the sorted order `normVal` produces).

`FloatRoundTrip` is first attempted as a theorem: in Lean 4.35 `Float` has a kernel model, and
`ratToFloat (floatToRat? x)` reduces to `Float.ofScientific (m * 5^k) true k` scaled back, which
is exact for a value with at most 53 significant bits. If the model of `Float.ofScientific` makes
this proof impractical, `FloatRoundTrip` stays a named hypothesis of `roundtrip` only (never an
axiom), and the tests that echo floats rely on their concrete instances, which the kernel
computes. Each concrete instance is a theorem:

```lean
/-- The instance of FloatRoundTrip at one float, decided by the kernel for each float a test
    sends through a port (for example 0.1, -0.25, 3e10, -1e-7, 123456.789 of PortEchoFloatTest). -/
def floatRoundTripAt (x : Float) : Bool :=
  match floatToRat? x with
  | some q => isNegZero x || (ratToFloat q).toBits == x.toBits
  | none => true
theorem roundtrip_at (hτ : τ.Canon) (he : Enc τ v j) (hx : NoExc τ v)
    (hF : (floatsOf v).all floatRoundTripAt = true) : Dec τ j (normVal v)
```

`floatsOf v` lists the float components of `v`; `roundtrip_at` is `roundtrip` with the hypothesis
restricted to those floats (the proof of `roundtrip` uses `FloatRoundTrip` only at them).

The exceptions are shown to be needed:

```lean
theorem a88_roundtrip_negzero : enc .float (.sv (.float (-0.0))) = some (.num 0) ∧
    dec .float (.num 0) = some (.sv (.float 0.0)) ∧ isNegZero (-0.0) ∧ ¬ isNegZero 0.0      -- kernel
theorem roundtrip_nan_fails : enc .float (.sv (.float fNaN)) = some .null ∧ dec .float .null = none
theorem roundtrip_just_nothing :
    enc (.maybe (.maybe .int)) (.con conJust [.con conNothing []]) = some .null ∧
    dec (.maybe (.maybe .int)) .null = some (.con conNothing [])                              -- kernel
```

### The property of task reduction (`sec:effects-tasks`)

```lean
inductive RedexRed : Val → Option Action → Val → Prop
  | andThenSucceed : AppVal f v t → RedexRed (.andThen f (.succeed v)) none t
  | andThenFail    : RedexRed (.andThen f (.fail v)) none (.fail v)
  | onErrorFail    : AppVal f v t → RedexRed (.onError f (.fail v)) none t
  | onErrorSucceed : RedexRed (.onError f (.succeed v)) none (.succeed v)
  | prim           : Out π vs t → RedexRed (.prim π vs) (some ⟨π, vs, t⟩) t

theorem taskRed_iff : TaskRed tk a tk' ↔ ∃ fs r r', focus tk = some (fs, r) ∧ RedexRed r a r' ∧ tk' = plug fs r'

/-- An outcome has no reduction. -/
theorem taskRed_outcome : tk.isOutcome = true → ¬ TaskRed tk a tk'

/-- Either every reduction is silent or every one is labelled, by one π and one argument list. -/
theorem taskRed_kind (h1 : TaskRed tk a1 t1) (h2 : TaskRed tk a2 t2) :
    (a1 = none ↔ a2 = none) ∧
    ∀ x1 x2, a1 = some x1 → a2 = some x2 → x1.prim = x2.prim ∧ x1.args = x2.args

/-- Silent reductions have the same right-hand side up to the choice of a member of APPLY. -/
theorem taskRed_silent_same (h1 : TaskRed tk none t1) (h2 : TaskRed tk none t2) :
    t1 = t2 ∨ ∃ fs f v w1 w2, AppVal f v w1 ∧ AppVal f v w2 ∧ t1 = plug fs w1 ∧ t2 = plug fs w2

/-- No reduction only when an application of r:e-task-andthen-succeed or r:e-task-onerror-fail
    has no result (for a well-formed task: every node a task form, every kill argument a pid). -/
theorem taskRed_none (hw : WFTask tk) (ho : tk.isOutcome = false) (hn : ∀ a t, ¬ TaskRed tk a t) :
    ∃ fs f v, (focus tk = some (fs, .andThen f (.succeed v)) ∨ focus tk = some (fs, .onError f (.fail v)))
              ∧ ¬ ∃ t, AppVal f v t
```

Method: `taskRed_iff` by induction on `TaskRed` (→) and on the frame list (←); the corollaries
by `taskRed_iff` and case analysis on `RedexRed` (the redex is determined by `focus`, so two
reductions share it). `taskRed_none`: `focus` of a well-formed non-outcome task is `some`, and
`Out` is non-empty at sleep, spawn and kill (kill of a pid).

### Executable counterparts

```lean
theorem stepTaskL_sound : (stepTaskL o n fr tk k).out = .value (a, tk') → TaskRedL tk a tk' (stepTaskL o n fr tk k).log
theorem stepTaskL_complete : TaskRedL tk a tk' l →
    ∃ fr, CompleteFor (fun o m k => stepTaskL o m fr tk k) (a, tk') l
theorem stepTaskL_unique (h : stepTaskL o n fr tk k = ⟨.value (a, t), l, k⟩)
    (hs : ∀ x, a = some x → x.prim ≠ .spawn) :
    ∀ a' t' l', TaskRedL tk a' t' l' → a' = a ∧ t' = t ∧ l' = l
theorem recvL_sound : (recvL o n c x k).out = .value v → RecvL c x v (recvL o n c x k).log
theorem recvL_complete : RecvL c x v l → CompleteFor (fun o m k => recvL o m c x k) v l
theorem recvL_unique : recvL o n c x k = ⟨.value v, l, k⟩ → ∀ v' l', RecvL c x v' l' → v' = v ∧ l' = l
theorem recvNone_sound : recvNone c x = true → ¬ ∃ v, Recv c x v
theorem flat_leaves : flat c = some cs → ∀ c' ∈ cs, (leafCore c').isSome
theorem flat_none : flat (.batch []) = some [] ∧ flat (.batch [.batch [], .batch []]) = some []
```

Method: induction on the task (structural) for `stepTaskL`, using `appVal_sound` and
`AppValL.complete`; for completeness at spawn, `fr` is the identifier in the action; at sleep and
kill any `fr`. The `_unique` theorems as step 1's `evExp_unique_l` (from completeness, `appVal_mono`
and `appVal_indep`); `stepTaskL_unique` excludes spawn, whose outcome identifier the rule leaves
free (`Out(spawn, tk)` is every `succeed pid`). `recvL`
likewise on the leaf. `recvNone_sound` by `cases` and `dec_iff`.

### `ME0` entries (D3)

```lean
/-- Each non-recursive text derives its literal value in the environment of the earlier texts. -/
theorem taskTexts_eval : ∀ k, ∀ x p ps e, taskTexts[k]? = some (.fn x (p :: ps) e) →
    EvalDec (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k)))
      (.val (.var x (lams (p :: ps) e) none))
      [(x, .closure p (lams ps e) (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k))) [])]
theorem listTexts_eval : ...   -- foldl and foldrHelper by r:d-dec-rec, reverse and foldr by r:d-dec-nonrec
theorem taskTexts_evalL : ...  -- the same with EvalDecL and log []
theorem VE_TaskIface_literal : VE_TaskIface_lit = VE_TaskIface   -- the literal written in the file
```

Method: as `elmTexts_eval` (`Theorems.lean`): the lemma `elmText_derivation` with the
non-recursiveness side condition decided by the kernel; a new lemma `elmTextRec_derivation`
(`r_d_dec_rec`, `isRecursive ... = true`) for the two recursive texts; the logged versions from
`r_d_exp_lambda_l` (log `[]`). The literal check by a Boolean structural comparison of closures
(their phrases and environments) decided by the kernel.

### Rulings

```lean
-- A74: the boundary is defined over JSON (with byte sequences, A92); Json.Encode.Value is JSON.
theorem a74_value_enc : Enc .value v j ↔ v = .bv j ∧ j.isJson = true
theorem a74_value_dec : (∃ v, Dec .value j v) ↔ j.isJson = true
theorem a74_nonfinite_null : Enc .float (.sv (.float fNaN)) .null ∧
    Enc .float (.sv (.float fInf)) .null ∧ Enc .float (.sv (.float (-fInf))) .null     -- kernel
theorem a74_maybe_float_null : Dec (.maybe .float) .null (.con conNothing [])

-- A76: objects are unordered; error reports are outside the definition.
theorem a76_mkObj_perm : kvs.Perm kvs' → (kvs.map (·.1)).Nodup → BVal.mkObj kvs = BVal.mkObj kvs'
theorem a76_enc_record_perm : r.Perm r' → enc (.record fs) (.record r) = enc (.record fs) (.record r')
theorem a76_enc_record_canon : τ.Canon → enc τ v = some j → j.Canon
-- decoding ignores further keys: adding a key absent from the type leaves the result unchanged
theorem a76_dec_extra_key : (l ∉ fs.map (·.1)) → dec (.record fs) (BVal.mkObj ((l, j) :: kvs)) = dec (.record fs) (BVal.mkObj kvs)
theorem a76_dec_missing_key : (l ∈ fs.map (·.1)) → (l ∉ kvs.map (·.1)) → dec (.record fs) (.obj kvs) = none

-- A88: JSON numbers are exact; no sign on zero; non-finite floats are null; too large decodes
-- to an infinity; no NaN decodes.
theorem a88_negzero_enc : Enc .float (.sv (.float (-0.0))) (.num 0)                       -- kernel
theorem a88_zero_dec_float : Dec .float (.num 0) v → v = .sv (.float 0.0) ∧ ¬ isNegZero 0.0
theorem a88_zero_dec_int : Dec .int (.num 0) v ↔ v = .int 0
theorem a88_huge_dec_float : Dec .float (.num (jnum 1 400)) (.sv (.float fInf))           -- kernel
theorem a88_no_nan : Dec .float j (.sv (.float x)) → x.isNaN = false
theorem a88_int_exact : Enc .int (.int n) (.num n) ∧ (intMin ≤ n → n ≤ intMax → Dec .int (.num n) (.int n))
theorem a88_int_range : (¬ ∃ v, Dec .int (.num (2 ^ 63)) v) ∧ (¬ ∃ v, Dec .int (.num (jnum 15 (-1))) v)

-- A92: byte sequences are not JSON; only a byte sequence decodes at Bytes; Value carries none.
theorem a92_bytes_not_json : (BVal.bytes os).isJson = false
theorem a92_dec_bytes : Dec .bytes j v ↔ ∃ os, j = .bytes os ∧ (∀ o ∈ os, o < 256) ∧
    v = .con conBin [Val.ofList (os.map (Val.int ·))]
theorem a92_bytes_not_string : ¬ ∃ v, Dec .string (.bytes os) v
theorem a92_bytes_not_list : ¬ ∃ v, Dec (.list .int) (.bytes os) v
theorem a92_value_no_bytes : Enc .value v j → j.isJson = true
theorem a92_bytes_nested : Enc (.list .bytes) (Val.ofList [binv [1, 2]]) (.arr [.bytes [1, 2]])  -- kernel
```

Methods: the concrete ones by the kernel after rewriting with `enc_iff`/`dec_iff`; the general
ones by `dec_iff` and `simp [dec]` (or induction for `a76_enc_record_perm`, using that `fmLookup`
on a key-unique list is invariant under `Perm`; `Val` records from evaluation have unique keys,
which is a hypothesis `(r.map (·.1)).Nodup`). `a76_mkObj_perm`: `mergeSort` of a key-unique list
gives the unique strictly sorted permutation (`List.Perm` and sortedness lemmas of core).

### Examples (`Eff/Examples.lean`, acceptance)

```lean
-- Task.perform identity (Task.succeed 1) evaluates, in the test basis, to a task leaf
theorem ex_perform : ∃ v, EvalExp E_ex (ap (qv "Task" "perform") [v "identity", ap (qv "Task" "succeed") [i 1]]) v ∧
    ∃ t, v = .leaf .task t                                                                    -- kernel
-- Task.sequence [succeed 1, succeed 2, ..., succeed 6] reduces by stepTaskL to succeed [1..6]
-- (six elements exercise foldrHelper's four-element unrolling and its recursion)
theorem ex_sequence : iterateTask 200 (seqTask 6) = some (.succeed (Val.ofList ((List.range 6).map (fun k => .int (k+1)))))  -- kernel
-- Task.attempt on a failing task gives a task whose success value is Err
theorem ex_attempt_err : ...                                                                  -- kernel
-- Cmd.batch [Cmd.none, Cmd.none] flattens to the empty multiset
theorem ex_flat_none : ...                                                                    -- kernel
```

`E_ex` is the environment a module that imports `Task` sees (step 2's import of `ME0_Task`).
`iterateTask n t` applies `stepTaskL (.const false) fuelT 0 t 0` until an outcome, with `TaskRed` soundness
giving the chain of derivations.

## Translator changes

None. Chapter 8 is reached only by worker programs (step 5) and by port declarations, whose
payload types the translator writes from step 3 on in the format of `PTy` above (record fields
sorted by label; `PTy.normalise` is applied by the Lean side to whatever the translator writes, and
`PTy.Canon` is checked by the kernel for every port of every generated program in a generated
theorem `ports_canon_<Shard>`).

## Tests gained

None (0). The counts of every earlier step are unchanged.

## Acceptance

Commands as in [conventions.md](conventions.md). Expected:

- `lake build`: no `sorry`, no new warnings. New files: the twelve of the table.
- `lake exe run-examples`: `Total: N checks, N agree, 0 diverge (0 known); K theorems by decide
  +kernel.` with N and K exactly as after step 3 (no test added or changed).
- `lake env lean scripts/check-axioms.lean`: every theorem of this step uses only `propext`,
  `Classical.choice`, `Quot.sound`; none uses `native_decide`.
- The constructor parity test: 39 book constructors (7 + 15 + 14 + 3) each with one `_l` twin, and
  the auxiliaries `EncSeq`, `EncOpt`, `EncFields`, `DecSeq`, `DecOpt`, `DecFields` with theirs.
- These theorems exist and are proved: `enc_iff`, `dec_iff`, `Enc.functional`, `Dec.functional`,
  `enc_total`, `roundtrip` (with `FloatRoundTrip` as theorem or as hypothesis, reported which),
  `taskRed_iff`, `taskRed_outcome`, `taskRed_kind`, `taskRed_silent_same`, `taskRed_none`,
  `stepTaskL_sound`, `stepTaskL_complete`, `recvL_sound`, `recvL_complete`, `taskTexts_eval`,
  `listTexts_eval`, the A74, A76, A88 and A92 theorems listed above, and the four examples.
- Memory: no new file above 2 GB resident (none imports `Lean`); the clean build within the budget
  of the conventions.
- Translator `--check` up to date; `elm-test` unchanged; `pnpm test:all` and
  `node runner/check-baseline.js` unchanged.
- Site: `runner/mechanisation-data.js` links the 39 `r:e-*` rule pages to their constructors
  (`r_e_<slug>`); rule count includes `Eff/EncDec.lean`, `Eff/Task.lean`, `Eff/Messages.lean`;
  link audit 0 problems.
- Reports: README Files table (twelve rows), "What the theorems say" gains Chapter 8 with the trust
  tags (`[params]` for the empty platform, `[harness]` unchanged); the mechanisation report's
  update block; the plan's status line.

## Risks and fallbacks

- **Nested inductives and `deriving`.** `PTy` and `BVal` nest `List (String × _)` and `Option`;
  if `deriving DecidableEq` or structural recursion over them is refused, write the instances and
  the functions as mutual definitions over explicit list auxiliaries (as `eqSet`/`eqList`/`eqRec`
  are today).
- **`eqSet` and kernel cost.** `eqSet` grows by ten cases; every existing kernel theorem that
  reduces an equality pays for the larger match. Measure the build before and after; if the peak
  rises above the budget, split the effect cases into a helper `eqEff` called from one catch-all
  case.
- **`FloatRoundTrip`.** May not be provable with reasonable effort against Lean's Float model.
  Fallback stated above: a named hypothesis of `roundtrip` only, and concrete instances by the
  kernel.
- **Kernel cost of the Task texts.** `Task.sequence` through `foldrHelper` evaluates many closures;
  `ex_sequence` measures it. If it is slow, the example is reduced to three elements (still
  exercising `foldrHelper`'s three-element case) and the six-element case is a `native_decide`
  theorem listed as native.
- **Step 2 changes its shapes.** This specification follows step 2's specification of
  2026-11-11 (`Val.batch`, `Val.mapE`, `Val.prog`, `PTy` with `tuple2`/`tuple3`). If step 2's
  implementation changes them, the `flat`, `leafCore`, `Recv`, `eqSet` and tuple cases follow; the
  rule constructors do not change.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **Logged twins of `Enc` and `Dec` carry only the empty log.** D4 asks for a logged relation
   beside each relation of the book. `Enc` and `Dec` have `AppVal` premises (the array rules), so
   their twins are added (`EncL`, `DecL`, with `encL_log_nil`), but no derivation of them can log.
   Proposed: D4 should say that a relation gets a logged twin when one of its rules has a premise
   that is a logged judgement whose log can be non-empty; then `EncL`/`DecL` are dropped and the
   logged rules of Chapters 8 and 9 use `Enc`/`Dec` directly. Followed meanwhile (twins added).
   Dispatch (step 5) has no application premise at all and gets no twin under either reading.
2. **D5 and boundary values.** D5 says boundary (JSON) values are constructors of `Val`. The book
   puts only JSON values in `Val` (JVal ⊆ Val), while a leaf of an outgoing port holds any boundary
   value, byte sequences included (CmdVal admits `Val ∪ BVal`). The single constructor `Val.bv`
   therefore admits non-JSON boundary values, and the class is recovered by the predicate
   `Val.WF`. This is a representation choice within D5, recorded so that a reader does not take
   `Val.bv` to be JVal.

## Progress

**2026-11-11: Chapter 8 in Lean.**

- `Eff/Boundary.lean`: `BVal` with arrays and objects in the explicit list types `BArr` and `BObj`
  of a mutual block (Lean 4.35 derives no `DecidableEq` through `List` nesting, as for `PTy`);
  `jnum`, `isDecimal`, `BVal.canonB`, `isJson`, `mkObj`, `floatToRat?` (through `dyadic`),
  `ratToFloat`, `isNegZero`.
- `Objects.lean`: `Prim`, `Mgr`, the eight new `Val` constructors, the ten new basic values
  (`taskSucceed` to `arrayToList`; the port values were step 2's), `conArr`, `conBin`,
  `conPerform`, `isOutcome`, `isTask`; `isCmdSub` accepts leaves. `Show.lean` prints them.
  `Apply.lean`: the `Apply` constructors of Figure fig:effects-apply, the ports and the arrays;
  their executable part `applySetEff` (kept apart, as `applySetNew` is), its soundness,
  completeness and `applySetEff_length` (at most one member); `eqSet` clauses 3 and 4 for the new
  values (boundary values compared as terms, being canonical).
- `Eff/EncFn.lean`: `enc` and `dec`, structural on the payload type, lists by `mapM` (a first
  version recursing on values as well compiled by well-founded recursion, which the kernel cannot
  unfold). `Eff/EncDec.lean`: the 29 rules, `enc_iff`, `dec_iff`, `Enc.functional`,
  `Dec.functional`. No logged twins (the plan's disposition of issue 1).
- `Eff/Task.lean`: the 7 rules and their twin, `focus`, `plug`, `RedexRed`, `taskRed_iff`,
  `taskRed_outcome`, `taskRed_kind`, `taskRed_silent_same`, `WFTask`, `taskRed_none`,
  `stepTaskL` with `stepTaskL_sound`, `stepTaskL_complete`, `stepTaskL_unique`.
- `Eff/Flat.lean`: `flat`, `leafCore`, `flat_leaves`, `flat_none`. `Eff/Messages.lean`: the 3
  rules and their twin, `recvL`, `recvL_sound`, `recvL_complete`, `recvL_unique`, `recvNone_sound`.
  The twin check covers `TaskRed` and `Recv`.
- `Eff/TaskTexts.lean`: the texts of elm/core 1.0.5, checked against the package sources (List.elm
  lines 150 to 261, Task.elm lines 117 to 317). `<<` is left-associative, as the book's Figure
  fig:core-fixities and Basics.elm declare it (this specification's remark that it is
  right-associative was wrong; for composition the grouping does not change the value). One
  general theorem, `textValue_eval` (and `textValue_evalL`), derives every text's value, by
  r:d-dec-rec for foldl and foldrHelper (`listTexts_recursive`) and r:d-dec-nonrec otherwise;
  `taskTexts_eval`, `listTexts_eval` and `taskTexts_evalL` are its instances. The values are
  computed definitions, not literals written out; nothing recomputes them in a test theorem until
  step 5. ME0 gains `Task` and `Process`; `ME0_good` covers them.
- `Eff/Properties.lean`: `apply_effect_singleton`; A74 (`a74_value_enc`, `a74_value_dec`,
  `a74_nonfinite_null`, `a74_maybe_float_null`), A76 (`a76_enc_record_perm`,
  `a76_dec_missing_key`), A88 (`a88_negzero_enc`, `a88_zero_dec_int`, `a88_int_exact`,
  `a88_int_range`, `a88_huge_dec_float`), A92 (all six); `PTy.Canon`, `floatToRat?_decimal`,
  `HasPTy`, `enc_total`.
- `Eff/Examples.lean`: `ex_perform`, `ex_sequence` (six tasks, 2.1 s and 1.8 GB), `ex_attempt_err`,
  `ex_flat_none`, by the kernel through a structural equality of first-order values (`eqFO`,
  proved sound), values having no decidable equality.
- The site counts 109 rules (Chapters 6 to 9) and links theorems that name `r_e_*` to their pages.
- 2,129 theorems, 0 axiom problems; 1,585 checks unchanged.

Differences from this specification:
- Lean's `Float` is opaque to the kernel (a float's bits, `Float.ofScientific`), so the theorems
  about particular floats (`a74_nonfinite_null`, `a88_negzero_enc`, `a88_huge_dec_float`) are
  `native_decide`, tagged `[native]`, against the specification's "none uses native_decide".
  `a88_zero_dec_float` and `a88_no_nan` are not proved: no theorem about `ratToFloat` holds for all
  rationals without a model of the C library's rounding. `HasPTy` at `Value` requires the JSON
  value to be canonical, without which `enc_total`'s canonicity is false; for the same reason
  `a76_enc_record_canon` is not stated for arbitrary values.

**2026-11-11: step 4 completed.**

- `Eff/MkObj.lean`: `a76_mkObj_perm` (sorting by insertion gives a permutation sorted by key, and
  two such of one key-unique list are equal, `List.Perm.eq_of_pairwise`) and `a76_dec_extra_key`
  (a lookup in `mkObj kvs` finds the last binding, `lookup_mkObj`).
- `Eff/Normalise.lean`: `PTy.normalise`, `PTy.distinctB`, `normalise_canon`; the translator emits
  `ports_canon_<Shard>` in every checks shard (all ports of every program, helpers included,
  canonical, by the kernel).
- `Eff/WF.lean`: `BadBv`, `Val.WF`, `wf_out_leaf`, `wf_bv_iff`, `wf_ofList`.
- `Eff/RoundTrip.lean`: `NoExc`, `FloatRoundTrip`, `roundtrip` (through the function form `rt`,
  mutual with `rtList` and `rtFields`), `a88_roundtrip_negzero` and `roundtrip_nan_fails`
  (`native_decide`, floats), `roundtrip_just_nothing` (kernel).
- 2,493 theorems, 0 axiom problems.

Differences from this specification:
- `FloatRoundTrip` is a named hypothesis of `roundtrip` (the specification's fallback). Lean's
  Float is opaque to the kernel and core has no lemma relating a float to its bits, so neither the
  fact nor its instance at one float (`floatRoundTripAt`, `roundtrip_at`) can be proved; those two
  are not stated.
- `NoExc` also requires a record's labels to be distinct: with a repeated label `labelsMatch`
  holds but the decoded record has each label once, so the property fails.
- `a88_roundtrip_negzero` states the sign of the decoded zero through `isNegZero` (values holding
  floats have no decidable equality).
- `dec_wf` (decoding gives well-formed values) is not stated; the specification asks only for
  `Val.WF`.