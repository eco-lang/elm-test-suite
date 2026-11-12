# Step 6: statements about every execution (`CHECK-NOT`)

Part of [the plan](../lean-full-definition.md); follows [conventions.md](conventions.md). Status:
specified 2026-11-11, not started.

Book references are to `definition/tex/programs.tex` (Chapter 9) and `definition/tex/effects.tex`
(Chapter 8) unless another file is named.

## Goal

Prove the three `CHECK-NOT` lines that the book supports as universal statements: in every
execution the book allows (under the test's host), at every derivation of every step, no log entry
prints with the forbidden pattern. The method is a per-test invariant (the third review's
decision; the earlier deadline-order abstraction was unsound, `part1.md` P1-11): a predicate on
configurations and host states, true after the start, closed under every transition rule under
the host relation, and implying that each step's log is free of the pattern. Non-derivability
facts come from structural inversion and, for the logs of applications of closures, from D1's
completeness of the logged evaluator.

| Test | `CHECK-NOT` | Host for which it is proved |
|------|-------------|-----------------------------|
| `tests/elm-core/src/TaskOnErrorSucceedTest.elm` | `handler called` | every host (`Host.any`); the program has no incoming port |
| `tests/elm/src/PortIncomingRejectTest.elm` | `received: null` | the echo host |
| `tests/elm/src/StandardA88PortNonFiniteTest.elm` | `Just` | the echo host |

The positive checks of the three tests are proved as in step 5. The step also settles finding T1
(StandardA81SleepBeyond32BitsTest) by a theorem that the book allows the line its `CHECK-NOT`
forbids, and sketches, as an optional stretch, an explorer with a zone abstraction.

Gains: these 3 tests.

## Prerequisites

Step 5 entire: `Config`, `Step`, `StepL`, `StartL`, `AcceptMsgsL`, `Dispatch`, `Host`,
`HostAllows`, `ExecL`, `WorkerExec`, `WorkerTest`, `holds_of_run`, the scheduler with overrides.
Step 4: `TaskRedL`, `RecvL`, `Dec`, `dec_iff`, `flat`, `leafCore`, `taskRed_iff`. Step 3:
`ModProgram`, `#mod_program_theorems` (the model for the generated conjunctions). Step 2:
`EvalProgramL`, `evProgram`, `Btest`, and `evProgram_unique_l` (below). Step 1
([step-01-core-foundations.md](step-01-core-foundations.md)): `LogCheck` (`.run` for CHECK-NEXT),
the logged evaluator `appVal (o : Oracle) : Nat → Val → Val → Nat → Res Val` (oracle `Nat → Bool`
read at an index `k`), and its completeness, monotonicity and oracle independence for the logged
relation, of which this step uses the consequence:

```lean
/-- A value found without reading a choice (the index comes back unchanged) is the only one, and
    so is its log. -/
theorem appVal_unique_l : appVal o n f v k = ⟨.value w, l, k⟩ → ∀ w' l', AppValL f v w' l' → w' = w ∧ l' = l
```

with step 4's `stepTaskL_unique` and `recvL_unique` built on it.

For the evaluation of the modules, step 2's uniqueness theorem (step 2's specification, "the
same seven statements" for `evProgram`):

```lean
theorem evProgram_unique_l : evProgram o n B p k = ⟨.value v, l, k⟩ →
    ∀ v' l', EvalProgramL B p v' l' → v' = v ∧ l' = l
```

## Lean definitions

### Files

| File | Namespace | Contents |
|------|-----------|----------|
| `Prog/Invariant.lean` | `StandardElm.Prog` | `renderEntry`, `containsStr`, `NoMatch`, `WorkerTest.HoldsNot`, `TestInv`, `TestInv.sound`, the determinism and inversion lemmas |
| `Prog/Inv/TaskOnErrorSucceedTest.lean` | `StandardElm.Prog.Inv.TaskOnErrorSucceedTest` | named values, the invariant, its proof, `checkNot` |
| `Prog/Inv/PortIncomingRejectTest.lean` | `StandardElm.Prog.Inv.PortIncomingRejectTest` | likewise |
| `Prog/Inv/StandardA88PortNonFiniteTest.lean` | `StandardElm.Prog.Inv.StandardA88PortNonFiniteTest` | likewise |
| `Prog/T1.lean` | `StandardElm.Prog` | the finding T1 theorem |
| `Prog/Explore.lean` (optional) | `StandardElm.Prog` | the zone explorer, if the stretch is done |

The three `Inv` files import `Generated/Worker01.lean` (the programs) and are imported by
`Generated/ChecksWorker01.lean` (the test theorems). None imports `Lean`.

### The universal statement (`Prog/Invariant.lean`)

The runner checks a `CHECK-NOT` pattern as a substring of the whole output
(`runner/directives.js`, `verifyPatterns`), and a pattern need not have the form `label: value`
(StandardA88PortNonFiniteTest's is `Just`). So the statement is about the printed entries, each
printed as Elm/JS's `Debug.log` prints it (`label: ` then the value), by `showElm`.

```lean
def renderEntry (e : String × Val) : String := e.1 ++ ": " ++ showElm e.2
/-- pat occurs in s (list infix on characters; reduces in the kernel). -/
def containsStr (pat s : String) : Bool := isInfixList pat.toList s.toList
def NoMatch (pat : String) (lg : Log) : Prop := ∀ e ∈ lg, containsStr pat (renderEntry e) = false

/-- CHECK-NOT pat: for every flags value and every execution under the test's host, with every
    derivation of its steps, no log entry prints with pat (D9, D1). -/
def WorkerTest.HoldsNot (w : WorkerTest) (pat : String) : Prop :=
  ∀ j lg, WorkerExec (Btest []) w.prog.modules w.flagsType j w.host lg → NoMatch pat lg

/-- The runner's reading: the whole output, entries joined by newlines, does not contain pat. -/
theorem noMatch_output (h : NoMatch pat lg) (hn : '\n' ∉ pat.toList) :
    containsStr pat (String.intercalate "\n" (lg.map renderEntry)) = false
```

`WorkerExec` quantifies over the logged executions; by `Exec.lift` (step 5) every execution of the
book has a logged version, so `HoldsNot` covers every execution of the book and every order of
logging that a logged derivation fixes (D4).

### The invariant framework

```lean
/-- A per-test invariant: main's record r0, a predicate I on configurations and host states,
    and the three obligations. -/
structure TestInv (w : WorkerTest) (pat : String) where
  r0 : List (String × Val)
  I  : Config → List BVal → Prop
  prog_ok  : ∀ v lm, Mod.EvalProgramL (Btest []) w.prog.modules v lm → v = .prog r0 ∧ NoMatch pat lm
  start_ok : ∀ j K0 ls, StartL (portEnv w.prog.modules) w.flagsType j r0 K0 ls → I K0 [] ∧ NoMatch pat ls
  step_ok  : ∀ K hs a K' l hs', I K hs → StepL (portEnv w.prog.modules) r0 K a K' l →
               HostAllows w.host hs a hs' → I K' hs' ∧ NoMatch pat l

theorem TestInv.sound (T : TestInv w pat) : w.HoldsNot pat
theorem holdsNot_any (T : TestInv { w with host := .any } pat) : w.HoldsNot pat
```

`TestInv.sound`: unfold `WorkerExec`; `prog_ok` gives `r = r0` (injectivity of `Val.prog`) and
the module log; `start_ok`; induction on `ExecL` with `step_ok`; `NoMatch` of an append is the
conjunction. `holdsNot_any`: every `HostAllows w.host` step is a `HostAllows .any` step with the
same host state (constructor `any`), and the invariant does not read the host state.

### Determinism and inversion lemmas (`Prog/Invariant.lean`)

These are the only places where non-derivability is needed. The first is where D1's completeness
is used.

```lean
/-- D1, as this step uses it: every logged derivation of an application whose evaluation reads no
    choice has the computed value and log. -/
theorem appValL_det (h : appVal o n f v k = ⟨.value w, l, k⟩) :
    ∀ w' l', AppValL f v w' l' → w' = w ∧ l' = l := appVal_unique_l h
```

`appVal_unique_l` is where D1's completeness enters: step 1 proves it from the completeness of
the logged evaluator (`AppValL.complete`), fuel monotonicity and oracle independence. Every use
below instantiates `h` by a kernel computation with `o = Oracle.const false`, `k = 0` and
`n = fuelT`, whose result has `next = 0` (no function equality is reached in these programs).

The structural inversions (each by `cases` on the derivation; the constructors whose conclusion
does not unify are discharged by `cases` itself):

```lean
theorem taskRedL_outcome : tk.isOutcome = true → ¬ TaskRedL tk a t l
theorem taskRedL_andThen_inner (ho : t.isOutcome = false) :
    TaskRedL (.andThen f t) a t' l → ∃ t'', TaskRedL t a t'' l ∧ t' = .andThen f t''
theorem taskRedL_andThen_succeed : TaskRedL (.andThen f (.succeed v)) a t l → a = none ∧ AppValL f v t l
theorem taskRedL_onError_succeed : TaskRedL (.onError f (.succeed v)) a t l → a = none ∧ t = .succeed v ∧ l = []
theorem taskRedL_prim : TaskRedL (.prim π vs) a t l → l = [] ∧ ∃ x, a = some x ∧ x.prim = π ∧ x.args = vs ∧ Out π vs t
theorem recvL_task : RecvL (.leaf .task tk) x w l → x = .val w ∧ l = []
theorem recvL_port : RecvL (.leaf (.inn p τ) f) x w l →
    ∃ j v', x = .port p j ∧ dec τ j = some v' ∧ AppValL f v' w l
theorem appValL_conv (h : 0 < k.arity) : AppValL (.con k []) v w l → w = .con k [v] ∧ l = []
theorem acceptMsgsL_one (hdet : ∀ v l, RecvL c x v l → v = m ∧ l = []) (hex : Recv c x m) :
    AcceptMsgsL [c] x Ms l → Ms = [m] ∧ l = []
theorem dispatch_nil : Dispatch s P Q H [] P' Q' H' → P' = P ∧ Q' = Q ∧ H' = H
theorem dispatch_task1 (hc : leafCore c = some (.task, tk)) : Dispatch s P Q H [c] P' Q' H' →
    ∃ n, n ∉ fmDom P ∧ P' = P.set n (.live ⟨tk, s, some c⟩) ∧ Q' = Q ∧ H' = H
theorem dispatch_outs (hc : ∀ c ∈ L, ∃ j, leafCore c = some (.out p, .bv j)) :
    Dispatch s P Q H L P' Q' H' → P' = P ∧ H' = H ∧
    ∃ js, fmLookup Q p = some js ∧ Q' = fmPlus Q [(p, js ++ L.filterMap outValue)]
theorem perm_nil : L.Perm [] → L = []
theorem perm_one : L.Perm [c] → L = [c]
theorem perm_two : L.Perm [c, c'] → L = [c, c'] ∨ L = [c', c]
theorem platStep_empty : ¬ PlatStep K a K'
```

(`outValue c` is `some j` when `leafCore c = some (.out _, .bv j)`; `r:p-disp-plat` is excluded
because `platMgrs = []`.)

For every test, `prog_ok` is one lemma: `evProgram (.const false) fuelT (Btest []) w.prog.modules 0`
is `⟨.value (.prog r0), [], 0⟩` (kernel), then `evProgram_unique_l`. The three programs' top-level
declarations are functions and `main = Platform.worker {...}`, so the module log is empty.

### Comparing values

`Val` has no decidable equality (Lean's `Float` has none). The invariants therefore name the
concrete values that occur (tasks, closures, messages) as Lean definitions obtained from the
evaluator's own output, and every equation between such values is proved by `rfl` (the kernel
checks definitional equality by evaluation), never by `decide` on `Val`. For example:

```lean
/-- init applied to () in TaskOnErrorSucceedTest, as the evaluator computes it. -/
def initOut : Res Val := appVal (.const false) fuelT fi .unit 0
def T1 : Val := match initOut.out with | .value (.tuple _ (.leaf .task t) none) => t | _ => .unit
theorem init_eval : appVal (.const false) fuelT fi .unit 0 = ⟨.value (.tuple .unit (.leaf .task T1) none), [], 0⟩ := rfl
```

and `T1` is then unfolded one constructor at a time (`T1 = .andThen C (.onError Hd (.succeed (.int 1)))`
by `rfl`, with `C` and `Hd` defined as projections in the same way).

## Theorems: the three invariants

In each, `w` is the generated `WorkerTest`, `PE = portEnv w.prog.modules`, `r0` main's record (computed),
`fi`, `fu`, `fs` its fields `init`, `update`, `subscriptions`. A configuration is written
`(s, v, M, P, sb, Q, H)` as in the book; `P = {n ↦ e}` means `P.get n = some e` and
`P.get q = none` for `q ≠ n`; `_` is any time.

### TaskOnErrorSucceedTest (`handler called`)

Values. `C` is the closure of `Task.map`'s `\a -> succeed (func a)` with `func = Got`; `Hd` is
`handler`; and

- `T1 = andThen(C, onError(Hd, succeed 1))`, the task of `Task.perform Got (Task.succeed 1 |> Task.onError handler)`;
- `T2 = andThen(C, succeed 1)`, `T3 = succeed (Got 1)`;
- `c = leaf(task, T1)`, `m = Got 1`, `none = batch()`.

Invariant `I(K, hs)`, for `K = (s, v, M, P, sb, Q, H)`:

> `v = ()`, `sb = none`, `Q = []`, `H = []`, and for some `n` one of
> (a) `P = {n ↦ (T1, _, c)}` and `M = ε`;
> (b) `P = {n ↦ (T2, _, c)}` and `M = ε`;
> (c) `P = {n ↦ (T3, _, c)}` and `M = ε`;
> (d) `P = {n ↦ ended}` and `M = m`;
> (e) `P = {n ↦ ended}` and `M = ε`.

The host state is not constrained: the program has no port, so `PE = []` and no `In` event has a
rule (`r:p-in-accept` and `r:p-in-reject` need `PE(p) = (in, τ)`). The theorem is proved for
`Host.any`.

Obligations.

- `prog_ok`: the module log is empty and main's value is `prog r0` (`evProgram_unique_l`).
- `start_ok`: `FlagsVal .unit j v1` gives `v1 = ()` for every `j` (A77); `appValL_det` with
  `init_eval` gives `fi () = ((), c)` with log `[]`; `flat c = [c]`, `perm_one`, `dispatch_task1`
  gives `P = {n ↦ (T1, 0, c)}`; `appValL_det` on `fs ()` gives `none` with log `[]`. Shape (a),
  log `[]`.
- `step_ok`, by `cases` on `StepL` (12 constructors) in each shape:
  - (a): `r:p-proc-step` only (no message, no queue, no port, no platform; `r:p-proc-message` and
    `r:p-proc-end` need an outcome). `taskRedL_andThen_inner` (the inner `onError(Hd, succeed 1)`
    is not an outcome), then `taskRedL_onError_succeed`: the step is silent, the new task is `T2`,
    the log is `[]`. **This is the point of the test**: `r:e-task-onerror-fail`, the only rule that
    applies `Hd`, needs `fail` inside the `onError`, and `succeed 1` is not `fail`. The labelled
    rules (sleep, spawn, kill) need a labelled reduction, which `taskRed_kind` excludes. `r:p-wait`
    stays in (a).
  - (b): `r:p-proc-step` with `taskRedL_andThen_succeed` and `appValL_det` on `C 1`: `T3`, log `[]`.
  - (c): `r:p-proc-message` with `recvL_task`: message `m`, log `[]`; `r:p-proc-end` is excluded
    (the task succeeds and the origin is a leaf); to (d).
  - (d): `r:p-update` with `appValL_det` three times: `fu m` is a closure `U` with log `[]`; `U ()`
    is `((), none)` with log `[("result", 1)]`; `fs ()` is `none` with log `[]`; `flat none = []`,
    `perm_nil`, `dispatch_nil`. To (e).
  - (e): only `r:p-wait`.
- Logs: every step's log is `[]` or `[("result", 1)]`, which prints `result: 1`; neither contains
  `handler called` (kernel).

```lean
theorem checkNot : w_elm_core_TaskOnErrorSucceedTest.HoldsNot "handler called" := holdsNot_any inv
```

### PortIncomingRejectTest (`received: null`)

`PE = {echoOut ↦ (out, Maybe String), echoIn ↦ (in, String)}`; host `echo echoOut echoIn`.

Values. `S = leaf(in(echoIn, String), Received)` (the subscription, constant);
`m = Received "ok"`; the boundary values `null` and `"ok"` (`.str "ok"`).

Invariant `I(K, hs)`:

> `v = ()`, `sb = S`, `P = {}` (no process ever exists), `H = []`,
> `Q = {echoOut ↦ js}` with every member of `js` in `{null, "ok"}`,
> every member of `hs` in `{null, "ok"}`,
> every member of `M` equal to `m`.

Obligations.

- `start_ok`: `fi ()` is `((), batch [leaf(out echoOut, null), leaf(out echoOut, "ok")])` with log
  `[]` (`appValL_det`; the encodings by `enc` at `Maybe String`: `Nothing` to `null`, `Just "ok"`
  to `"ok"`); `perm_two` (either order); `dispatch_outs`: `P = {}`,
  `Q = {echoOut ↦ js}` with `js` one of `[null, "ok"]`, `["ok", null]`; `fs ()` is `S` with log `[]`;
  `hs = []`.
- `step_ok`:
  - `r:p-update` (head `m`): `fu m` a closure, log `[]`; applied to `()`, `((), none)` with log
    `[("received", "ok")]`; `fs ()` is `S`, log `[]`; empty dispatch. Invariant kept.
  - `r:p-proc-*`: excluded, `P = {}`.
  - `r:p-out` on `echoOut`: the head `j` of `js` leaves `Q`; `HostAllows` `out_echo` appends `j` to
    `hs`; `j ∈ {null, "ok"}`. (`out_other` is excluded: `Q` has no other port.)
  - `In(p, j)`: `HostAllows` admits only `in_echo`, so `p = echoIn` and `j` is the head of `hs`.
    If `j = null`: `dec String null = none` (`dec_iff`), so `r:p-in-accept` is excluded and
    `r:p-in-reject` leaves `K` unchanged, `hs` loses its head. If `j = "ok"`: `r:p-in-reject` is
    excluded (`Dec` holds); `r:p-in-accept` with `flat S = [S]`, `perm_one`,
    `acceptMsgsL_one` (via `recvL_port` and `appValL_conv`: `Received` applied to `"ok"` is `m`,
    log `[]`): `M` gains `m`.
  - `r:p-wait`: kept. `r:p-platform`: `platStep_empty`.
- Logs: `[]` or `[("received", "ok")]`, which prints `received: "ok"`; it does not contain
  `received: null` (kernel).

The echo host is needed: under `Host.any` the host may send the string `received: null`, which is
accepted and logged as `received: "received: null"`, containing the pattern.

```lean
theorem checkNot : w_elm_PortIncomingRejectTest.HoldsNot "received: null" := TestInv.sound inv
```

### StandardA88PortNonFiniteTest (`Just`)

`PE = {echoOut ↦ (out, Float), echoIn ↦ (in, Maybe Float)}`; host `echo echoOut echoIn`.

Values. `C1` is the closure of `Task.map`'s `\a -> succeed (func a)` with `func = always Start`;
`T1 = andThen(C1, prim(sleep, 10))` (the task of `Task.perform (always Start) (Process.sleep 10)`,
`10` a float); `T2 = andThen(C1, succeed ())`; `T3 = succeed Start`; `c = leaf(task, T1)`;
`S = leaf(in(echoIn, Maybe Float), Got)`; the messages `Start` and `g = Got Nothing`.

Invariant `I(K, hs)`:

> `v = ()`, `sb = S`, `H = []`,
> `Q = {echoOut ↦ js}` with every member of `js` equal to `null`,
> every member of `hs` equal to `null`,
> every member of `M` in `{Start, g}`,
> and for some `n`, `P = {n ↦ e}` with `e` one of `(T1, _, c)`, `(T2, _, c)`, `(T3, _, c)`, `ended`.

(`Start` may be queued at most once in fact, but the invariant does not need the count.)

Obligations.

- `start_ok`: `fi ()` is `((), c)`; `dispatch_task1`; `Q = {echoOut ↦ []}`; `fs ()` is `S`.
- `step_ok`:
  - process `n` with `T1`: `taskRedL_andThen_inner`, `taskRedL_prim`: the only reduction is
    labelled by `sleep(10)` with outcome `succeed ()`; `r:p-proc-step` is excluded (its label must
    be a platform primitive, `platPrims = []`); `r:p-proc-sleep` gives `T2` (whatever the time, if
    `SleepReady` holds), log `[]`; spawn and kill rules are excluded by the primitive.
  - `T2`: `r:p-proc-step` with `appValL_det` on `C1 ()`: `T3`, log `[]`.
  - `T3`: `r:p-proc-message`: `Start` joins `M`; `n` ended.
  - `r:p-update`, head `Start`: `fu Start` then `()`: `((), batch [leaf(out echoOut, null), leaf(out echoOut, null)])`
    with log `[]` (`Enc_Float(NaN) = null` and `Enc_Float(+∞) = null`, `r:e-enc-float-null`, A88);
    `dispatch_outs` appends two `null`s; `fs ()` is `S`.
  - `r:p-update`, head `g`: log `[("got", Nothing)]`, empty dispatch.
  - `r:p-out`: `null` moves to `hs`.
  - `In(echoIn, null)` (`in_echo`): `dec (Maybe Float) null = Nothing`, so `r:p-in-reject` is
    excluded; `r:p-in-accept` with `acceptMsgsL_one`: `Got` applied to `Nothing` is `g`.
  - `r:p-wait`: kept.
- Logs: `[]` or `[("got", Nothing)]`, which prints `got: Nothing`; it does not contain `Just`.

The echo host is needed: under `Host.any` the host may send `1.5`, which `Maybe Float` decodes as
`Just 1.5`, and the log would print `got: Just 1.5`.

```lean
theorem checkNot : w_elm_StandardA88PortNonFiniteTest.HoldsNot "Just" := TestInv.sound inv
```

### Finding T1 (StandardA81SleepBeyond32BitsTest)

Step 5 translates this test with its positive check only. This step proves that the book allows
the line its `CHECK-NOT` forbids, so the omission is a finding and not a gap:

```lean
/-- r:p-wait lets 3e9 ms pass before the 200 ms sleep's action is taken; then the long sleep's
    action is ready, and the process logs before it is killed. -/
theorem t1_a81_long_sleep_may_end :
    ∃ j lg, WorkerExec (Btest []) w_elm_core_StandardA81SleepBeyond32BitsTest.prog.modules .unit j .none lg ∧
      ∃ e ∈ lg, e.1 = "the long sleep ended"
```

Proof: `runWorker` on the test with one override, `wait 3000000000` at the scheduler index at
which the default strategy chooses `wait 200` (found by `lake exe run-examples --trace
StandardA81SleepBeyond32BitsTest`, a new option of `Main.lean` that prints each scheduler index,
choice and event), then `runWorker_sound` and a kernel check of the log. After the wait both
sleepers are due; the 200 ms process runs first (earlier deadline), its message is handled, the
update dispatches the kill as a new process at the back of the run queue, and the long-sleep
process, ahead of it, takes its sleep action and logs. The override is recorded in
`definition/mechanisation/worker-choices.json` under the key
`"elm-core/StandardA81SleepBeyond32BitsTest#t1"` (a key with `#` is not a test and is not
translated; `Prog/T1.lean` writes the override directly). The test's page shows this theorem
beside the positive one, under the heading "not required by the book (finding T1)".

### Generated theorems

The translator (step 5's worker path) stops refusing these three tests (`checks:check-not`).
`WorkerTest` gains a field `checkNots : List String := []`, the patterns of the test's `CHECK-NOT`
lines, and step 5's `#worker_theorems` command emits, for a test whose `checkNots` is not empty,
the conjunction with the hand theorem, whose name is fixed by convention,
`StandardElm.Prog.Inv.<TestName>.checkNot`:

```lean
/-- tests/elm-core/src/TaskOnErrorSucceedTest.elm  [parse] [elab] [harness] [params] -/
theorem t_elm_core_TaskOnErrorSucceedTest :
    w_elm_core_TaskOnErrorSucceedTest.Holds ∧ w_elm_core_TaskOnErrorSucceedTest.HoldsNot "handler called" :=
  ⟨Prog.holds_of_run (by decide +kernel), Prog.Inv.TaskOnErrorSucceedTest.checkNot⟩
```

and likewise for the other two (the positive part of StandardA88PortNonFiniteTest is step 1's
`LogCheck.run` for its `CHECK` and `CHECK-NEXT`). If a test has more than one pattern, the second
conjunct is the conjunction over them. The translator fills `checkNots` only for tests listed in
a new list `checkNotProofs` in `Directives.elm` (the three names); any other test with a
`CHECK-NOT` stays refused `checks:check-not`.

## The explorer (optional stretch)

Not needed for the three tests. It would let a `CHECK-NOT` be proved without writing an
invariant, for programs whose reachable configurations are finite up to time and process
identifiers. It is specified here so that it can be taken up later; it is not part of this step's
acceptance.

**Why zones.** A deadline is `s' + max(0, d)`, fixed when the process reaches the sleep, and
`r:p-wait` lets any `d > 0` pass. Whether a later deadline falls before an earlier one depends on
differences of times against constants, so the order of deadlines alone is not a sound abstraction
(third review). The configurations with their times form a timed automaton: one clock per live
process, `x_n = s - s'_n` (the time since process `n` last stepped); `r:p-wait` advances every
clock by `d`; any step of process `n` resets `x_n` to 0; `r:p-proc-sleep` has the guard
`x_n ≥ c_n` with `c_n = max(0, q)`, a rational constant read from the task. The guards are
diagonal-free, so difference-bound matrices (DBMs) over the clocks, with the standard
`k`-extrapolation by the largest constant, give a finite, sound and complete abstraction of the
times (Bengtsson and Yi, "Timed Automata: Semantics, Algorithms and Tools", 2004).

**Abstract configurations.**

```lean
/-- A configuration with its times removed and its process identifiers renamed canonically (in
    order of first occurrence in a fixed traversal of the configuration, values included). -/
structure Untimed where ...
/-- A DBM over the clocks of the live processes, entries (bound : Rat, strict : Bool) or ∞. -/
structure DBM where ...
structure AbsConfig where
  core : Untimed
  zone : DBM
  hs   : List BVal
/-- K and host state hs are represented by Z: K's untimed part, after canonical renaming, is
    Z.core, and the clock values s - s'_n satisfy Z.zone. -/
def γ (Z : AbsConfig) (K : Config) (hs : List BVal) : Prop

/-- All abstract successors, with the event and the log of each step. Applications are computed
    by the logged evaluator; where it consults a choice of APPLY, both answers are followed. -/
def absSucc (c : Ctx) (Z : AbsConfig) : Outcome (List (Option Event × Log × AbsConfig))
```

**Lemmas.**

```lean
theorem absSucc_sound (hZ : γ Z K hs) (hs' : StepL PE r K a K' l) (hh : HostAllows h hs a hs'') :
    absSucc c Z = .value S → ∃ Z', (a, l, Z') ∈ S ∧ γ Z' K' hs''
theorem absSucc_complete (hS : absSucc c Z = .value S) (hm : (a, l, Z') ∈ S) (hK' : γ Z' K' hs') :
    ∃ K hs, γ Z K hs ∧ StepL PE r K a K' l ∧ HostAllows h hs a hs'
/-- A set of abstract configurations closed under absSucc (with extrapolation and inclusion of
    zones), computed with fuel; `none` if not closed within the fuel. -/
def explore (c : Ctx) (Z0 : AbsConfig) (fuel : Nat) : Option (List AbsConfig)
theorem checkNot_of_explore (h : explore c Z0 n = some S) (hinit : start's abstraction is Z0)
    (hlogs : ∀ Z ∈ S, ∀ x ∈ (absSucc c Z).getD [], NoMatch pat x.2.1) (hmod : module log ok) :
    w.HoldsNot pat
```

Soundness alone (`absSucc_sound`) is what `checkNot_of_explore` needs; completeness
(`absSucc_complete`, exact without extrapolation and up to the extrapolation's bisimulation with
it) would make the explorer usable for "the book allows this log" as well. The applications'
logs and values are made deterministic by `appValL_det` where no choice is consulted; a consulted
choice branches.

**Limits.** Termination needs finitely many reachable untimed configurations up to renaming: a
program that spawns without bound (ProcessSpawnRecursiveTest is bounded; a general program need
not be), keeps a growing model, or a growing message queue, is beyond it, and `explore` returns
`none`. The host state is part of the abstract configuration, so the echo host's pending list must
stay bounded too.

## Translator changes

1. `Directives.elm`: a list `checkNotProofs` of the three test names; for them `CHECK-NOT` lines
   are kept as patterns and the test is translated; the conjunction theorem above is emitted.
2. The manifest entries of the three tests record `"checkNot": ["handler called"]` (and so on) and
   `"checkNotProof": "StandardElm.Prog.Inv.<TestName>.checkNot"`.
3. `worker-choices.json` gains the `#t1` entry (documentation only; the translator skips keys with
   `#`).
4. `Main.lean`: the option `--trace <TestName>`; for a translated `CHECK-NOT`, `run-examples`
   checks that the default run's log does not contain the pattern (a sanity check, not the
   theorem) and counts it as a check.

## Tests gained

3: PortIncomingRejectTest (`tests/elm/src`), StandardA88PortNonFiniteTest (`tests/elm/src`),
TaskOnErrorSucceedTest (`tests/elm-core/src`).

Their check lines: PortIncomingRejectTest `CHECK` 1, `CHECK-NOT` 1; TaskOnErrorSucceedTest `CHECK`
1, `CHECK-NOT` 1; StandardA88PortNonFiniteTest `CHECK` 1, `CHECK-NEXT` 1, `CHECK-NOT` 1. Seven
lines.

## Acceptance

Commands as in [conventions.md](conventions.md). Expected, relative to the counts after step 5:

- Translator: translated `T5 + 3` (578 if every earlier step delivered its count); no test that compiles is
  refused `checks:check-not` or `checks:directive:CHECK-NEXT` any more (of the `elm-spec` tests that
  compile, only these three and StandardA81SleepBeyond32BitsTest had such a refusal, and the last
  is translated with its `CHECK-NOT` dropped in step 5); `--check` up to date; `elm-test` passes, with a unit test that
  each `checkNotProofs` name is a test that has a `CHECK-NOT`.
- `lake build`: no `sorry`, no new warnings.
- `lake exe run-examples`: `N + 7` checks if step 3 counts a `CHECK-NEXT` line as a check of its
  own (`N + 6` if it counts it with its `CHECK`), all agreeing; `K + 3` theorems by
  `decide +kernel` (the three conjunctions, whose positive parts are by the kernel and whose
  universal parts are the hand proofs, themselves checked by the kernel without `native_decide`).
- `scripts/check-axioms.lean`: `checkNot` of each test, `TestInv.sound`, `appValL_det`,
  `t1_a81_long_sleep_may_end` use only `propext`, `Classical.choice`, `Quot.sound`.
- Memory: each `Inv` file measured on its own; within the budget (the invariant proofs unfold the
  programs' closures with `rfl`; expected below 3 GB each).
- `pnpm test:all` and `node runner/check-baseline.js` unchanged.
- Site: the three test pages show both the positive theorem and the universal one, with the host
  under which it holds and the trust tags `[parse] [elab] [harness] [params]`; the A81 test's page
  shows `t1_a81_long_sleep_may_end`; link audit 0 problems.
- Reports: mechanisation report (the three universal theorems, the hosts, finding T1 as a
  theorem), README ("What the theorems say": universal statements, per-test invariants), the
  preface's count, the plan's status line.

## Risks and fallbacks

- **Elaboration cost of `cases` on large concrete values.** The invariants contain closures with
  whole module environments. `cases` on `StepL` with such indices can be slow to elaborate.
  Fallback: state each shape with opaque names (`T1` etc. as `@[irreducible] def`s, unfolded only
  inside the lemmas that compute with them), so that `cases` unifies against constants.
- **A choice is read.** `appValL_det` needs evaluations that read no choice of APPLY (no
  comparison of two functions). None of the three programs compares functions; if a future test's
  does, its invariant must allow both results of the comparison (each found by an oracle), which
  `AppValL.complete` supports.
- **The printer.** `NoMatch` is about `showElm`'s text. For the logged values here (`1`, `"ok"`,
  `Nothing`) `showElm` agrees with Elm/JS's `Debug.log` output by construction; a different printer
  could only matter for a value whose printed form contains the pattern.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **PortIncomingRejectTest needs the echo host.** The plan's inventory says "(with the echo
   host)" for StandardA88PortNonFiniteTest only, and review P1-11 says PortIncomingRejectTest's
   `received: null` "never occurs for any host" because a String prints quoted. That is not so: a
   host may send the String `received: null`, which is accepted at a `String` port and logged as
   `received: "received: null"`, a line that contains the pattern. The statement is proved under
   the echo host, as for StandardA88PortNonFiniteTest; TaskOnErrorSucceedTest, with no incoming
   port, holds under every host. The plan's table should say "with the echo host" for both port
   tests.
2. **`CHECK-NOT` is a statement about printed entries.** D9 makes positive checks structured
   statements (`Expect.holds`) and says only regex and `CHECK-SAME` checks are compared as text.
   A `CHECK-NOT` pattern need not be `label: value` (`Just`), and the runner matches it as a
   substring of the output, so the universal statement here is about `showElm`'s text of each
   entry (`NoMatch`), with `noMatch_output` relating it to the runner's whole-output reading. D9
   should list `CHECK-NOT` with the text-compared checks.

## Progress

**2026-11-11: done (the optional explorer is not built).**

- `Prog/Invariant.lean`: `renderEntry`, `isInfixList`, `containsStr`, `NoMatch`,
  `WorkerTest.HoldsNot`, `TestInv`, `TestInv.sound`, `holdsNot_any`; `appValL_det`, `taskRedL_det`,
  `recvL_det`, `acceptMsgsL_one`, `dispatch_nil`, `dispatch_task1`, `dispatch_outs`, `perm_one`,
  `perm_two`, the host inversions, and Boolean shape checks with their equations (`Res.eq_get`,
  `pair_eq`, `taskLeaf_eq`, `flat_two`, `outLeaf_eq`, ...).
- `Prog/Inv/TaskOnErrorSucceedTest.lean`, `Prog/Inv/PortIncomingRejectTest.lean`,
  `Prog/Inv/StandardA88PortNonFiniteTest.lean`: the invariants as specified, each with `checkNot`.
  Every fact about the evaluator's results is one Boolean (`facts`) decided by the kernel.
- `Prog/T1.lean`: `t1_a81_long_sleep_may_end`, by the kernel, with the override `wait 3000000000` at
  scheduler iteration 6.
- Translator: `Directives.checkNotProofs`; `WorkerTest.checkNots`; the worker checks shard imports
  the three `Inv` files; `#worker_theorems` emits the conjunction. run-examples has a row per
  CHECK-NOT. 109 unit tests.
- 579 tests (the three gained); 1,708 checks, all agreeing; 2,751 theorems, 0 axiom problems.

Differences from this specification:
- The statement that a printed log entry does not contain the pattern is `native_decide`: the
  printer (`showVal`) is defined by well-founded recursion, which the kernel does not unfold. So
  the three `checkNot` theorems and the three generated conjunctions are tagged `[native]` (the
  specification expected "kernel" for the logs). Everything else in the invariants is the kernel's.
- `noMatch_output` (the runner's reading of the whole output) is not stated.
- `T1` is not recorded in `worker-choices.json`: `Prog/T1.lean` writes the override directly, as
  the specification allows; the test's page names the theorem in the reason for the dropped line.
- The explorer (optional stretch) is not built.

