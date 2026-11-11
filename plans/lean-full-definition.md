# Plan: encode the rest of the definition in Lean

**Status (2026-11-10): proposed.** Part I (Chapters 7, 8 and 9) was revised after an adversarial
review; Part II (the static semantics) was added afterwards, and the whole was reviewed again (see
"Reviews"). Not started. This plan follows phase 6 of
[elm-to-lean-translator.md](elm-to-lean-translator.md), and is a prerequisite for translating
groups E, G, J and K of [untranslated-tests.md](untranslated-tests.md).

The Lean mechanisation (`definition/mechanisation/standard-elm-mech`) encodes Chapter 6 (the
dynamic semantics of the Core) and the part of APPLY that the Core needs. This plan adds the rest
of the book, in two parts:

- **Part I, the rest of the dynamic semantics:** Chapters 7, 8 and 9 (steps 0 to 6).
- **Part II, the static semantics:** Chapters 4 and 5, Appendix C, the derived forms of Appendix
  A, the syntactic restrictions of Chapters 2, 3 and 9, and the static rules of Chapter 9 (steps 7
  to 11).

After both, these remain outside Lean:

- the concrete syntax (lexical analysis, layout and the grammar: Chapters 2 and 3 and Appendix B),
  for which the translator's parser, elm-syntax, stands in;
- the entries of Appendix D not yet encoded: `Ok` and `Err` and `logBase` (group B of
  untranslated-tests.md, a small separate step) and the values of `Bytes`;
- Appendix E, which records implementations rather than defining anything.

Theorems about the tests are stated in a test basis, B0 extended by the harness basis (problem 2)
and, for the library tests, by the core library's interfaces; that extension is outside the book
by design.

# Part I: Chapters 7, 8 and 9

## Goal

Part I adds the rest of the dynamic semantics:

| Chapter | File | Dynamic rules | What it defines |
|---------|------|--------------:|-----------------|
| 7, Dynamic Semantics for Modules | `dynamic-modules.tex` | 20 | interfaces, module environments, imports and their merging, exposing, record alias constructors, ports bound to values, top-level value groups |
| 8, Tasks, Commands, Subscriptions and Ports | `effects.tex` | 39 | effect values, task reduction, flattening, encoding and decoding at ports, the messages of leaf commands, APPLY on the effect values |
| 9, Programs | `programs.tex` | 20 | evaluation of a program's modules, `main`, configurations, dispatch, start with flags, transitions, traces |

(Counts of `\defnrule`. Chapter 9 has 23, of which 3 are static, `r:p-stat-module`,
`r:p-stat-main-program` and `r:p-stat-main-view`; these and `r:p-program`'s static premise are not
encoded here. See problem 1.)

The static semantics (Chapters 4 and 5, Appendix C, and Chapter 9's static rules) is Part II.
Part I does not wait for it: it trusts the translator's elaboration (problem 1), and Part II
removes that trust.

## Tests it brings in

From `definition/mechanisation/translation-manifest.json` (2026-11-09), by what each test needs.
The translator records only the lowest-ranked of a test's refusals (`Convert.elm`), so a test
refused for `effects` may need more. The review checked the sources of all of these for library
functions; the counts below are what remains after that. Step 0 confirms them.

| Tests | Kind | Needs |
|------:|------|-------|
| 9 | user modules (group G) | Chapter 7, the harness basis (problem 2) |
| 5 | record alias constructors (group C) | Chapter 7 (`r:dm-topdec-alias`) |
| 15 | port modules whose `main` is a view and which never use their ports (`CovPort*`, `PortEncoding*`) | Chapter 7, with the port basic values and payload types (which `r:dm-topdec-port-*` binds, never applied) |
| 9 | `Debug.log` as output (group E) | the instrumented evaluation (step 3); PureRecursiveValueThunkTest and PureMutualRecursiveValueTest also Chapter 7's thunk translation |
| 36 | `Platform.worker` programs with positive checks | Chapters 8 and 9, the instrumented evaluation, the host model. Two need no execution: ListLiteralDebugLogKindTest logs while a top-level value is evaluated (and uses `CHECK-DAG`), and NoImportsTest's `init` logs |
| 3 | worker programs with `CHECK-NOT` that the book supports | statements about every execution (step 6); StandardA88PortNonFiniteTest only for executions with the echo host |
| 2 | worker programs with `CHECK-NOT` that the book does **not** support | findings, not theorems (see "Findings of Part I") |
| 6 | need a library | stay out for now. With [core-library.md](core-library.md): NonEntryMainEvaluatedOnceTest (`String.repeat` in its helper), CoreIssue1123NestedCmdBatchStackOverflowTest (`List.foldl`, `List.range`), PortEchoArrayStringTest (`Array.empty`, `Array.fromList`). Outside elm/core: PlatformManagerCommandTest (`Random`, a platform manager), StandardA92BytesPortTest (`Bytes.Encode`, `Bytes.Decode`, and `List.map`, `Maybe.withDefault`), PortEchoJsonValueTest (`Json.Encode.encode`) |

So the plan gains up to 77 tests (29 + 9 + 36 + 3), and records 2 findings about tests. The
library tests of group H (Array, Dict, Bitwise) come in with the core library plan.

## Problems to settle first

### 1. The static semantics is not encoded, so elaboration is trusted

The dynamic rules take facts from elaboration: a port's direction and payload type (reduced syntax
of Chapter 7), the order of the modules, the default copy of `main` and the copies made by number
specialisation, and the type of `main`, which decides whether a program is a view or a program
value and gives its flags type. The translator computes these, as it already computes number
specialisation, and the Lean program carries them as data. Every theorem is about the reduced,
specialised program the translator writes. It is not about the source, and it does not show that
the program elaborates. Until Part II's step 10, the README and every test's mechanisation page
must say so.

### 2. `main = Html.text "done"` has no meaning in the book

Appendix C puts `Html` in ME0 for its type only. Its dynamic interface is empty
(`appendix-dynamic-basis.tex`: "VirtualDom and Html are (∅, {}, {})"), so `Html.text` is no value
of the basis, and a program whose `main` is `Html.text "done"` (the shape of almost every view
test) does not elaborate in B0. Today the translator keeps `main`'s `let` and drops only its
`text` body (`construct:main-shape`, `Convert.elm`). That works for one module. It cannot cover
helper modules whose top-level values call `Html.text` (CompilerIssue2119View's `renderView`,
EntryAuxWithMain's `main`, NonEntryMainAux's `main`), which Chapter 9 evaluates whether or not
they are used (`r:p-dyn-module`).

So a **harness basis** is needed. `Html` is already in ME0, with its type `Html` and nothing else,
so the harness basis replaces ME0's `Html`, statically and dynamically: its static interface binds
`text` with the scheme `∀msg. String -> msg Node` (elm/html's `text : String -> Html msg`), and its
dynamic interface binds `text` to one opaque basic value of arity 1, whose APPLY gives an opaque
value of a new kind that only this extension makes. Part I needs only the dynamic half; Part II
needs both (551 of the 633 compile-success tests use `Html.text` and nothing else outside B0). It
is stated as an assumption about the test harness, outside the book, and every theorem that uses it
names it.

Also record this in the ambiguity log: under B0, the suite's standard test shape is outside the
definition. The book's choice is deliberate, but the About page and Appendix E should say how the
test suite stands to it.

### 3. `Debug.log` output is outside the definition

APPLY(`Debug.log`, s, v) = {v}, and "any output it makes lies outside" the definition (Appendix D;
Appendix E, `appendix-implementation.tex` from line 541). Yet nearly every check reads that
output, and in a worker the logged expression sits inside `init` or `update`, where it mentions
local variables and cannot be evaluated on its own.

- **An instrumented relation, not only an instrumented evaluator.** A soundness theorem that
  forgets the log constrains nothing in it. Instead, define the instrumented judgements, the
  book's rules with a log threaded through each (a `Debug.log` application adds its entry; every
  other rule concatenates the logs of its premises in one fixed order). Then prove two things: an
  instrumented derivation forgets to a derivation of the book (so its value is the book's); and the
  instrumented evaluator is sound for the instrumented relation. Each log entry is then the
  `(s, v)` of an occurrence of APPLY(`Debug.log`, s, v) in a derivation of the book, listed in one
  linear order of that derivation.
- **Order.** Appendix E (`appendix-implementation.tex`, around line 533) leaves unordered only
  the bindings of a `let` that do not depend on each other. Groups follow their dependencies. The
  fixed order of the instrumented rules is one the book allows. A check about order (`CHECK-NEXT`)
  holds in that order, and its page says that the book allows others.
- **Counting.** A top-level value outside a recursive group is evaluated once (A59). A member of
  a recursive group is reached through its thunk (`dynamic-modules.tex`, Section
  `sec:dynamic-modules-groups`), so each reference evaluates it again and logs again. Appendix E
  also lets an implementation evaluate a top-level value on first use (eco), so a log in an unused
  top-level value may never print. A check that relies on a top-level value's log being printed,
  exactly once or at all (StandardA87NumberDefaultCopyTest), agrees with the book's evaluation but
  is not required by the book, and its page says so.
- **Matching.** The runner searches the whole of stdout and stderr for each `CHECK` pattern as a
  substring, with `{{regex}}` parts, in any order (`runner/directives.js`, `verifyPatterns`);
  `CHECK-DAG` is read as `CHECK`; `CHECK-NOT` searches the same way; `CHECK-NEXT` and
  `CHECK-SAME` constrain lines. The statements follow the runner: the log, printed line by line as
  Elm/JS prints `Debug.log` (`label: ` and `Debug.toString` of the value), contains the pattern.
- **A program with no meaning.** StandardLetStrictTest and StandardApplicationStrictTest
  (`EXIT: 1`), which translate today, put `Debug.todo` in `main`'s `let`. In module form `main`
  has no value, so the program has no meaning (`programs.tex`, `r:p-dyn-main`'s comment, A62),
  and their check `before: ()` has no derivation to be about. The instrumented evaluator still
  gives the log up to the point where evaluation stops. The statement for such a test is: every
  instrumented derivation attempt reaches `Debug.todo` with that log, and the program has no
  meaning. Stating this needs a judgement for a stuck evaluation, which step 3 defines.

### 4. Chapter 9 is a nondeterministic transition system

APPLY gives sets, `Process.spawn` chooses a fresh identifier, a batch's leaves are dispatched in
any order (A66, A67), and processes, port deliveries, incoming values, waiting and updates
interleave in every way the rules allow (A78, A86). A test's run is one execution.

- **Positive checks are existential.** A scheduler, a deterministic strategy that picks the next
  transition, produces one execution. Its soundness theorem says each step it takes is a
  transition derivable by the rules, and, with problem 3's instrumented relation, that each logged
  line comes from an APPLY(`Debug.log`, ...) in the derivation of one of its steps. Then "the log
  of this execution contains the CHECK patterns" shows that the book admits what the test expects.
  The scheduler takes its choices as parameters (the leaf order of each dispatch, which live
  process steps next), as the Core evaluator takes `ch` for APPLY, and a test's translation fixes
  the choices that reproduce the observed run. CmdBatchOrderTest, for example, expects one order
  of a batch (`port: [5,4,3,2,1]`), which the book allows (A66) but does not require. A check that
  no choice reproduces is a finding about the book or the test.
- **`CHECK-NOT` is universal.** "No execution logs this pattern" needs every execution, and must
  say which host: the host may send any value on an incoming port at any time (`r:p-in-accept`),
  so only executions with the test's host model are meant. With time in the configuration
  (`r:p-wait` lets any d > 0 pass), there are infinitely many executions. Step 6 needs either an
  abstraction of time (only the order of the sleep deadlines matters) with an explorer proved
  complete for the transitions, or a proof by invariant for each test. It is the hardest part of
  the plan and comes last.

### 5. The host and the platform

The runner's JavaScript launcher (`runner/run.js`, `launcher`) passes `flags` only when the test
has a `-- FLAGS:` line, and otherwise leaves it out (JavaScript `undefined`, which Elm 0.19.1
rejects for a program whose flags type is unit: StandardA72AbsentFlagsTest). It installs the echo,
every value sent on `echoOut` sent back on `echoIn`, only when the program has both ports. The host
model follows the book where the launcher and the book differ: absent flags are null (A72), and
the test's page notes the difference. The scheduler's host strategy: after `Out(echoOut, j)`, take
`In(echoIn, j)`, when both ports exist, and send nothing else.

On the native target the runner skips port modules and tests with flags (`run.js`, "needs a
JavaScript host"), but 15 of the 36 positive worker tests have neither and run natively. For
them the model has no host events, which is the same as the echo model for a program without the
echo ports, so one model serves both targets.

The platform's parameters (Prim_plat, Mgr_plat, Ev_plat) are empty, so there are no platform
steps, and the `Random` and `Time` tests stay out until there is a platform model.

## Design

### Lean objects, in dependency order

1. **Payload types** (Chapter 5, Section `sec:static-modules-ports`): an inductive for the types τ
   with Port(τ) (Int, Float, Bool, String, Bytes, unit, Maybe, List, Array, 2- and 3-tuples, closed
   records, `Json.Encode.Value`), written by the translator from elaboration.
2. **Boundary values** (`BVal`): JSON values with byte sequences. They are not values of the
   language, but a command's leaf for an outgoing port holds one, so they come before `Val`.
3. **Values.** `Val` gains, in its mutual block (a task holds values and a record holds tasks):
   tasks (`succeed`, `fail`, `andThen`, `onError`, `prim`), commands and subscriptions (`batch`,
   `map`, `leaf`), managers (one of which, `in(p, τ)`, holds a payload type), process identifiers,
   program values and JSON values. Equality is extended by clause 4 of `fig:dynamic-basis-eq`
   (effect values of the same form). There is no order on effect values (`cmp` is for comparable
   types only). `showElm` prints them as Elm/JS does.
4. **Basic values.** `record(l1 ... ln)` (Chapter 7); `outport(p, τ)` and `inport(p, τ)`; the
   effect basic values of Figure `fig:effects-apply`, with `Task.command`; `Array.fromList` and
   `Array.toList` (bound to no identifier; the encoding and decoding of arrays use them). The Elm
   texts of `Task.map`, `Task.map2` to `Task.map5`, `Task.sequence`, `Task.mapError`,
   `Task.perform` and `Task.attempt` go in `InitialBasis.lean`, evaluated in `E_Task` with the
   hidden `Perform` and `command`; `Cmd.none` and `Sub.none` in the environments of
   `Platform.Cmd` and `Platform.Sub`. `Task.sequence` applies `List.foldr`, whose text names
   further elm/core functions; each is added by its text, as Appendix D says.
5. **Modules.** Chapter 7's reduced syntax (Module, Header, Imports, ExpList, ExpItem, the six
   TopDec forms, DatBind, ConBind, TypBind), with Interface, ModEnv and Basis, the merge of
   environments, the thunk translation of top-level value groups (Section
   `sec:dynamic-modules-groups`) as a function on Core phrases, and ME0 as a module environment.
   `Basis.lean`'s flat E0 is replaced by ME0 and the default imports, evaluated by the rules.
6. **Programs and execution.** Configurations, process maps, outgoing queues, the pending multiset
   H, events and traces (Figure `fig:programs-objects`).

### Relations, functions and their soundness

As for the Core, each judgement is an inductive relation with one constructor per rule, named
after its label (`r_dm_module`, `r_e_task_prim`, `r_p_update`, ...), with an executable
counterpart proved sound for it.

**Mutual dependency.** APPLY on an outgoing port is defined through Enc (`effects.tex`, the
meaning of `outport`), and Enc and Dec at arrays apply `Array.toList` and `Array.fromList` by the
application of values (`r:e-enc-array`, `r:e-dec-array`), a judgement of the Core. So the Core
relations, the APPLY relation and Enc and Dec form one mutual block. Since APPLY on
`Array.toList` and `Array.fromList` evaluates no closure, a simpler encoding is possible: Enc and
Dec as structural functions that unfold those two applications directly, with a lemma that each
unfolding is the application the rule's premise names. Step 4 decides which.

| Judgement | Executable | Soundness |
|-----------|------------|-----------|
| Chapter 7's sentences | `evModule`, `evProgram` (fuel) | result derivable |
| `tk →[a] tk'` | `stepTask` (with an outcome chooser for `r:e-task-prim`) | step derivable |
| `Enc_τ(v) = j`, `Dec_τ(j) = v` | `enc`, `dec` | result derivable (with APPLY, see above) |
| `c, receiving x, gives v` | `receive` | result derivable |
| dispatch, start, `K →[ℓ] K'` | `dispatch`, `start`, `step` (with a choice of transition) | step derivable |
| an execution | `run` (scheduler and host, fuel) | every step derivable, so the run is an execution; its log is the instrumented log of its steps |

### The book's properties as theorems

- Chapter 7: the property of interfaces (`dynamic-modules.tex`, Section
  `sec:dynamic-modules-compound`), on which `r:dm-expitem-alias` relies.
- Chapter 8: the property of task reduction (Section `sec:effects-tasks`); that Enc and Dec are
  partial functions, and the round trip (Section `sec:effects-ports`). The property's other
  clause, that every value elaboration admits as a payload has an encoding, needs the static
  semantics and is left out.
- Chapter 9: the guarantees of A86 (Section `sec:programs-execution`, the property after the
  transition rules), and the property that the order of a program's modules does not matter, for
  its dynamic half only.

### Translator

- **Programs as module sequences.** The translator resolves a test's imports among its sources
  (`tests/<project>/src`), orders the modules as elaboration does, and writes each module in the
  reduced syntax: headers and exposing lists, imports with their qualifiers, custom types, record
  aliases with their labels in the order written, ports with their direction and payload type, and
  top-level values, ordered and grouped by the derived form for modules of Appendix A (Section
  `sec:appendix-derived-forms-modules`). Number specialisation works across modules, with an
  exposing item standing for its copies.
- **All current translations move to module form.** Today a test's top-level definitions sit in a
  `let` around each check, and its constructors are bound directly (README, "Chapter 7 is outside
  this encoding"). With Chapter 7 encoded, every test is translated as the program it is, so that
  one form is proved. Every existing check must keep its value, except those of programs that have
  no meaning in module form (StandardLetStrictTest and StandardApplicationStrictTest, problem 3).
  Any other change is a finding about the `let` encoding or the module rules.
- **Checks.** A check becomes a statement about the instrumented log of the program's evaluation
  (a view) or of an execution (a worker).

## Steps

0. **Measure.** Lift the `effects` and `import:*` refusals in a dry run of the translator, and
   record every further refusal of each test, to confirm the counts above.
1. **Chapter 7 in Lean.** Payload types and boundary values; the port basic values and
   `record(...)`; Interface, ModEnv and the merge; the thunk translation; the 20 rules,
   `evModule` and its soundness; the program rules `r:p-dyn-module` and `r:p-dyn-main`; ME0 and
   the default imports; the harness basis (problem 2); the property of interfaces. Theorems for
   A25 (a delayed self-reference forced during its own evaluation has no result), A28 and A38
   (shared qualifiers merge, later imports replace earlier ones) and A82 (`main` need not be
   exposed), on small programs written by hand.
2. **Translator: module form.** Programs as module sequences. Move every translation, compare every
   check, and measure the build (now 6.3 GB at peak; a module form may cost more). Gains up to 29
   tests: user modules, record aliases, and the view tests with unused ports. Their checks are, for
   now, of the values of top-level expressions, as today.
3. **Instrumented evaluation.** The instrumented relations and evaluator, the two theorems of
   problem 3, the judgement for a stuck evaluation, and checks as statements about the log
   (`CHECK`, `CHECK-DAG`, `CHECK-NEXT`, `CHECK-SAME`, and `CHECK-NOT` for a single evaluation).
   Gains group E, up to 9.
4. **Chapter 8 in Lean.** Effect values, their equality and printing, APPLY on the effect values
   and the Elm texts of `Task`, `Platform.Cmd` and `Platform.Sub`, task reduction, flattening, Enc
   and Dec, messages, and their soundness and properties. Theorems for the rulings stated in this
   chapter: A88 (negative zero and non-finite floats at ports), A92 (bytes are not JSON), A74 and
   A76 (JSON values, records as objects).
5. **Chapter 9 in Lean, and the worker tests.** Configurations, dispatch, start with
   `Flags_τ`, the transitions, the scheduler with its choices, the host model, `run` and its
   soundness, the A86 guarantees. Theorems for the rulings stated in this chapter: A77 (unit
   flags), A79 to A81 (spawn, kill, sleep), A62 (an update with no result). The translator writes
   worker programs with their flags and the scheduler's choices. Gains up to 36 tests.
6. **Every execution.** An explorer over the executions of a program with its host model, with
   time abstracted, proved complete for the transition rules up to that abstraction, or a proof by
   invariant for each test. Gains the 3 `CHECK-NOT` tests the book supports, and lets an
   order-independent check be stated as holding in every execution where it does.

Each step: `lake build`, `lake exe run-examples`, the translator's unit tests and `--check`; the
site data and the site rebuilt, and the link audit; the README, the preface's count and the
mechanisation report updated. The site's rule pages for the `dm`, `e` and `p` rules link to their
Lean constructors as the Core rules' pages do.

## Risks

- **Build cost.** Moving every test to module form, and running executions, will raise the build's
  memory and time. The current form is already near what a laptop allows (6.3 GB). Shards may need
  to shrink. Execution checks may only be provable by `native_decide`, as the native checks are now.
- **Kernel reduction of executions.** `decide +kernel` over a scheduler run of hundreds of steps
  may be beyond the kernel, as WideRecordGcBitmapTest is beyond it now.
- **Universal statements (step 6)** may need more than an explorer: time, fresh process
  identifiers and unbounded message queues make the state space infinite, and only an abstraction
  proved sound and complete makes it finite.
- **Trust.** The theorems trust the translator for elaboration (problem 1) and the harness basis
  for `Html` (problem 2). Both must be stated on every page that shows a theorem.

## Findings of Part I

From the review, before any encoding. The test runner stays green: these concern what the book
requires, not what the implementations do.

- **ProcessKillRunnableTest's `CHECK-NOT: survived runnable` is not required by the book.**
  Between the parent's `Process.spawn runnableChild` and its `Process.kill`, the child may take
  its own steps (A78: "a process may be suspended at any andThen"; `programs.tex`, comment of
  `r:p-proc-step`): its `Process.spawn`, then the `andThen` that applies `\_ -> survive
  "runnable"` and logs. Both implementations kill it first, but the book allows the log.
- **StandardA81SleepBeyond32BitsTest's `CHECK-NOT: the long sleep ended` is not required by the
  book.** `r:p-wait` lets 3e9 ms pass, and `r:p-proc-sleep` sets no upper bound on the 200 ms
  sleep (its comment: "the definition sets no time by which the action must take place"), so the
  long sleep may end, and log, before the kill.

Each test should say in its description that its `CHECK-NOT` checks the implementations' behaviour
beyond the book's guarantee. Their translations would state the positive checks only. Whether the
book should give a stronger guarantee here (a bound on sleep, or a kill that precedes the child's
first step) is a question for the ambiguity log.

# Part II: the static semantics

## Goal

Part II encodes:

| Part of the book | File | Rules | What it defines |
|------------------|------|------:|-----------------|
| 4, Static Semantics for the Core | `static-core.tex` | 45 | type and row variables with classes, admissible types, substitution with rows, type functions, schemes and `≻`, the scope of explicit type variables, closure (with A93), elaboration of expressions, patterns, declarations and type expressions; the further restrictions (irredundancy, exhaustiveness, defaulting of `number`) |
| 5, Static Semantics for Modules | `static-modules.tex` | 19 | type names and their generation, interfaces, provider maps, port types (`Port(τ)`), elaboration of modules, imports, exposing, custom types and aliases. Its further restrictions defer to Chapter 9 |
| 9, Programs (static half) | `programs.tex` | 3, and `r:p-program`'s static premise | the program restrictions (Section `sec:programs-syntax`), elaboration of a program's modules in order, the type of `main` (a program or a view), the port environment |
| C, The Initial Static Basis | `appendix-static-basis.tex` | | T0, ME0 with the type schemes of the basis, E0, the default imports, OT_stat |
| A, Derived Forms | `appendix-derived-forms.tex` | | the derived forms as a function from the source syntax, including the grouping of a `let` and of a module's declarations |
| 2 and 3, Syntactic Restrictions | `syntax-core.tex`, `syntax-modules.tex` | | every restriction of Sections `sec:syntax-core-restrictions` and `sec:syntax-modules-restrictions`: rows, record updates, field selection, binding sites and shadowing, float patterns, annotation placement, `let` recursion, ports, headers, import aliases, the `Basics` qualifier, operator items, exposing, top-level patterns, distinct declarations, type-variable sequences, aliases not recursive, value recursion |

It has two aims, of different size.

1. **Positive: every program that compiles is legal.** For each compile-success test, a theorem
   that the program is legal: it elaborates by the rules, and meets the syntactic restrictions and,
   in its principal derivation, the further restrictions (`static-core.tex`, Section
   `sec:static-core-further`: a phrase whose principal derivation breaks one "is treated as a
   phrase that does not elaborate"; ruling A96), with the type of `main` and the port environment.
   Since every type has inhabitants (A97), the further restrictions give the same answer in every
   derivation, so for them the derivation the inference finds will do; only the type of `main`
   needs the principal derivation, and so principality (step 11), unless an annotation fixes it.
   Then number specialisation and the reduced syntax are computed in Lean, and
   Part I's trust in the translator's elaboration (problem 1) is retired, with the qualification of
   problem 11.
2. **Negative: every program that must be refused is not legal.** For each compile-error test, a
   theorem that no derivation exists, or that the principal derivation breaks a named restriction
   (A96); for exhaustiveness and irredundancy, any one derivation shows it (A97). The first is a
   statement about all derivations, and much harder.

## Tests it brings in

**Compile-success tests (633).** All 941 tests are `elm-spec`; 308 expect a compile error and 633
do not. In the book's basis B0, almost none of the 633 elaborate, because they use names that
Appendix C does not bind (a scan of the sources, 2026-11-10):

| Tests | What they need beyond B0 |
|------:|---------------------------|
| 42 | nothing: they elaborate in B0 |
| 551 | only `Html.text`, which Appendix C does not bind (`Html` is in ME0 for its type only) |
| about 40 | library functions or modules: `Tuple`, `List`, `Maybe` and `Array` functions, `Dict`, `Bitwise` (elm/core, outside the book), and `Random`, `Bytes.Encode`, `Bytes.Decode`, `Json.Encode` functions (outside elm/core) |

So the positive aim is stated in a **test basis**: B0 with the harness basis of problem 2 (which
must be static as well as dynamic), and, for the library tests, the interfaces of the core library
plan ([core-library.md](core-library.md)), whose type schemes are elm/core's annotations. Tests
that need modules outside elm/core stay out. Of the 633, three do not parse (the `Container*` tests
of group A, `[-3`) and five are refused as `construct:large-program`.

**Compile-error tests (308).** By the first `TAGS` entry of each test: `s-*` (static rules of the
Core) 220, `core-*` (Chapter 2 restrictions) 29, `modules-*` (Chapter 3 restrictions) 25, `sm-*`
(static rules of modules) 16, `p-*` (programs) 8, `fig:*-grammar` 7, `program-*` 3.

| Tests | Kind | Needs |
|------:|------|-------|
| about 12 | lexical: bad escapes (4), operator chains (4), layout (1), constants not separated (2), adjacent items (1) | parsing; out (problem 7) |
| 7 | grammar errors (`fig:*-grammar`) | parsing; out (problem 7) |
| about 50 | syntactic restrictions decided without types: the rest of `core-*` but exhaustiveness and irredundancy, `modules-*`, `program-*`, cyclic values and `main` referring to itself | step 8: deciders on the source syntax |
| 8 | exhaustiveness (6) and irredundancy (2) | types; step 9, at the inferred derivation (problem 12, A97) |
| about 230 | the static rules (`s-*`, `sm-*`, `p-*`): type errors, annotations too general, record extension, infinite types, unbound names, wrong `main` types, payload types | scope errors and type-expression errors (an annotated `main`, a port's payload type) in step 9; the rest complete inference, step 11 |

Step 7 checks every count, and classifies each compile-error test by the rule or restriction the
book says it breaks.

## Problems to settle first

### 6. The rules are declarative

The static rules are not syntax-directed: `σ ≻ τ` lets a derivation choose any instance, and
"where the premises of a rule leave a type in its conclusion undetermined, the derivation may
choose any type that satisfies them" (`static-core.tex`, Section `sec:static-core-rules`).

- **Positive, by an inference procedure in Lean proved sound.** The translator's
  `Translate/Infer.elm` (Hindley-Milner with let-polymorphism, rows, Appendix A's grouping and
  A93's closure) was written for number specialisation and falls well short of the rules:
  explicit type variables are flexible (no rigidity, no escape check, A20, A21); it knows only a
  few type constructors of the basis (`Result`, `Cmd`, `Sub`, `Task`, `Program`, `Html`, `Array`
  and `Value` give `unknown-type`); it handles one module, without imports, provider maps or type
  names (a type is a string, so a local type cannot be told from an imported one of the same
  spelling); it checks admissibility only for `number` (not `comparable`, `appendable` or
  `compappend` in list and tuple components); it does not tell row variables from type
  variables; and ports, workers and `main` are refused before it runs. Extending it to emit
  certificates would mean rewriting most of it, and then writing a checker in Lean. Instead, write
  the inference once, in Lean, over the book's objects, and prove it sound (whatever it infers is
  derivable) in step 9, and complete in step 11. Infer.elm stays as the translator's own, and the
  two are compared.
- **Negative, by completeness.** "No derivation exists" needs the inference to be *complete*: if
  any derivation exists, it finds a principal one. The standard route is constraint generation
  and unification over types with classes (a variable's class bounds what it may stand for,
  `fig:static-core-admissible`) and rows (A23), with generalisation at each group. Completeness
  for let-polymorphism with classes and rows, rigid explicit variables and A93's closure is a
  substantial proof. Mechanised completeness proofs of algorithm W exist (Naraschewski and Nipkow,
  Isabelle; the CakeML inferencer, HOL4), but none for this combination.

### 7. Parsing is not encoded

A compile-error test that elm-syntax cannot parse gives no syntax tree, and a theorem that such a
program is refused needs a parser in Lean, proved to accept exactly the grammar of Appendix B with
the layout rule. That is out of scope; those tests stay out. For the tests it does parse, step 7
checks that elm-syntax reads them as Elm does (the `[-3` failure of group A shows that it need not).

### 8. The source syntax, before the derived forms

Several restrictions are stated on the source, before the derived forms: `res:core-let-recursion`
tells `f x = ...` from `f = \x -> ...`, which the derived form erases, and
`res:core-annotation-placement` speaks of "source text". So Lean needs the source syntax, with
type expressions, annotations, custom types, aliases with their parameters, ports with their
types, headers with their exposing lists, and the derived forms as a Lean function from it. Today
`Derived.lean` has functions that build bare phrases, not a source datatype. The translator writes
the source syntax; Lean applies the derived forms (including the grouping of Appendix A), elaborates,
and computes the reduced syntax.

The translator has no path for this today: compile-error tests are refused from their directives
before parsing, and every other refusal (`Convert`, `Infer`, `Specialise`) comes before any
writing. A separate path writes the source syntax of any program elm-syntax parses, with no
inference.

### 9. What a compile-error test checks is not the book's

A compile-error test's `CHECK` line is the title of the compiler's report (224 of 374 such lines
are literal titles), a generic pattern (`{{-- [A-Z ]+ -}}`, in 83 tests), or, with `CHECK-NOT`,
the absence of crash text ("compiler bug", "HasCallStack", 53 tests). None of these is the book's.
The theorem says only that the program is not legal, naming the rule or restriction where it can,
and the test's page shows its directives for information.

### 10. Appendix C needs extracting

`Translate/Basis.elm` holds the type schemes of the basis, transcribed from Appendix C, and Lean
needs them too. The site's `runner/definition-data.js` keeps each row of Appendix C only as KaTeX
output, which nothing can be generated from. Write a small extractor for the rows of Appendix C's
figures (`\kw{name} & \mapsto & (scheme, status)`) into structured data, generate the Lean ME0
from it, and check `Basis.elm` against it.

### 11. One derivation is not every derivation

> **Resolved in the book, 2026-11-10 (ruling A95).** Chapter 4 now defines principal derivations
> (`sec:static-core-principal`) and states their existence as a property; defaulting is no longer
> restriction 3 but the first step of number specialisation, applied to the principal derivation
> and exempting variables bound by an annotation. What remains for Lean is unchanged: step 11
> proves the property (complete inference). Read "restriction 3" below as that default.

Number specialisation depends on the derivation: the type chosen for each integer literal and the
instance of each use. The rules let a derivation choose `Int` for an undetermined type directly,
and restriction 3 (defaulting of `number`) defaults only a *type variable* that no closure
generalises; read literally, a derivation that never introduces the variable escapes it, so
`2 ^ -1` would have derivations with different values. The book means the principal derivation,
with its remaining `number` variables taken as Float (A27, revised 2026-11-10 from Int). Proving that a given derivation is that one
needs principality, which is step 11. So step 10's end-to-end theorem says "for the derivation
the inference finds", and becomes "for the program" only after step 11.

Two things for the ambiguity log: restriction 3 should be stated in terms of the principal
derivation, not "a derivation"; and an annotation's explicit `number` variable is bound by
`∀U'` in `r:s-valbind-var`, not by a closure, so restriction 3, read literally, defaults it to Float.
Restriction 3 also selects a derivation rather than stating a condition on one, so it is not a
restriction like the others, and Lean encodes it as the choice of the principal derivation, not as
a predicate.

### 12. Inhabitants can be empty, and depend on the instance

The book's inhabitants of a type are finite phrases built from constructors and constants
(`static-core.tex`, Section `sec:static-core-further`), so a type whose every constructor needs an
argument of the type itself has none. `Never` is one: its only constructor, the hidden
`JustOneMore`, takes a `Never`. So is `type V = V V`. Two consequences, which are findings about
the book (see "Findings of Part II"):

- `Result Never Int` has no inhabitant `Err h`, so in
  `case r of Ok n -> n; Err e -> never e` the second branch covers no inhabitant, and the match
  breaks irredundancy. Elm accepts this common idiom.
- `Maybe Never` has the one inhabitant `Nothing`, so `case m of Nothing -> 0` is exhaustive at
  that type. Elm rejects it.

For the encoding: the decider for exhaustiveness and irredundancy must compute inhabitation (a
least fixpoint over the custom types), not use a standard pattern-matrix algorithm, which assumes
every constructor is inhabited.

> **Resolved in the book, 2026-11-10 (ruling A97): empty types.** Inhabitants may now be infinite
> (the book's clauses are read coinductively), so `V` has the inhabitant `V (V (V ...))`, `Never`
> has `JustOneMore (JustOneMore ...)`, every type has an inhabitant, and every constructor gives
> inhabitants at every instance. Elm 0.19.1 agrees on the five programs of the ruling, and both
> findings above are gone. For the encoding:
> - The decider is the standard pattern-matrix algorithm (usefulness, as in Elm's and eco's
>   `Nitpick/PatternMatches`), which takes every constructor to be possible; no inhabitation
>   fixpoint is needed.
> - The book's inhabitants are infinite trees. Lean encodes one as a map from positions (paths of
>   argument indices) to nodes, closed under the clauses, which avoids coinductive types; or the
>   proof works only with *cut-off* inhabitants: a pattern examines positions to its depth, so an
>   inhabitant may be replaced below the deepest pattern of a match by any filler, where only
>   wildcards and variables look. The decider is proved equal to the book's statement by this
>   lemma.
> - **Invariance lemma.** Where the principal derivation gives a part of a match's type as a type
>   variable, only patterns that cover everything elaborate there, and any instance of the
>   variable has inhabitants, which the same patterns cover. So the restrictions give the same
>   answer in every derivation: legality (for these restrictions) and the refusals by them need
>   only the derivation the inference finds, not principality.

> **Resolved in the book, 2026-11-10 (ruling A96): which derivation.** The restriction is about
> the derivation's type τ, and different derivations may give a match different instances; read
> literally, the book did not say which. Either reading failed: "some derivation" accepts
> `g r = case r of Ok n -> n` (take the error type to be `V`) and an unannotated `main` whose
> flags nothing fixes (take them to be `()`), both of which Elm rejects; "every derivation"
> rejects `h x = case x of _ -> 0` (take `x` to be `V`). The book now judges the further
> restrictions, and Chapter 9's type of `main`, on the principal derivation
> (`sec:static-core-principal`, `sec:static-core-further`, `sec:static-modules-further`, Chapter 9).
> So a refusal by exhaustiveness or irredundancy needs only the decider at the principal type, and
> a legality theorem needs the inferred derivation to be principal (step 11). With A97 (above),
> the restrictions give the same answer in every derivation, so for them the choice no longer
> matters; it still matters for the type of `main`.

## Design

- **Objects** (`static-core.tex`, Sections `sec:static-core-simple` to `sec:static-core-closure`;
  `static-modules.tex`, Section `sec:static-modules-objects`): type variables with classes, row
  variables, type names with arities, types with records and rows, admissible types as a decidable
  predicate, substitution (partial, for the row condition), type functions, schemes and `≻`,
  contexts with their explicit variables U, `Clos` with A93's extra closure over `number`
  variables, interfaces, provider maps, `Port(τ)`, and the static ME0, T0 and OT_stat.
- **Relations.** One inductive per judgement, one constructor per rule, named after its label
  (`r_s_atexp_scon`, `r_sm_module`, `r_p_stat_main_program`, ...), as for the dynamic rules.
- **Restrictions.** Each restriction of Chapters 2, 3, 4 and 9 as a predicate written as the book
  states it, with a decision procedure proved equal to it. Restriction 3 is the choice of
  derivation (problem 11). Exhaustiveness and irredundancy by the standard pattern-matrix
  algorithm, proved equal to the book's (coinductive) inhabitants; judged on the principal
  derivation (A96), which for them any derivation equals (problem 12, A97).
- **Inference** in Lean (problem 6): sound in step 9, complete in step 11.
- **Number specialisation in Lean** (step 10): the copies of Section `sec:dynamic-core-numbers` and
  the reduced syntax, computed from the inferred derivation, replacing the translator's
  `Translate/Specialise.elm` as the source of truth. The translator keeps its own copy, and the two
  are compared. Part I's translations, until then written by the translator in reduced syntax, are
  then derived in Lean from the source syntax.

## The book's properties and rulings as theorems

- Chapter 4: the property of admissible types under substitution (Section
  `sec:static-core-types`).
- Chapter 5: the properties of interfaces and of the type names a module generates.
- Chapter 9: the static half of the property that the order of a program's modules does not
  matter (Part I proves the dynamic half).
- Rulings, on small programs: A19 (classes from names), A20 and A21 (explicit variables), A23 (no
  duplicate labels by rows), A27 (defaulting), A35 (equality at every type), A36 (row variables),
  A93 (closure over `number`); and for modules A28, A29, A38 (imports and qualifiers), A32 and A82
  (`main`), A84 (port names), A92 (Bytes in payload types).

## Steps

7. **Measure and classify.** Classify every compile-error test by the rule or restriction it
   breaks, and by whether elm-syntax parses it, and parses it as Elm does. Recount the
   compile-success tests by what they need beyond B0. Extract Appendix C (problem 10).
8. **Source syntax, derived forms and the syntactic restrictions.** The source syntax in Lean; the
   translator's new path that writes it for any program elm-syntax parses; the derived forms of
   Appendix A as a Lean function; deciders for every restriction of Chapters 2, 3 and 9, proved
   equal to their statements. Gains the refusals decided without types, about 50, and, for every
   compile-success test, a theorem that it meets the syntactic restrictions.
9. **Chapters 4 and 5, Appendix C, the static rules of Chapter 9, and sound inference.** Objects,
   relations, the static ME0 generated from Appendix C, the test basis (problem 2, static half, and
   the core library's interfaces), and inference proved sound. Theorems that each compile-success
   test elaborates, and, with step 8 and the deciders for exhaustiveness and irredundancy at the
   inferred types, that it is legal (the further restrictions hold in every derivation once they
   hold in one, A97; the type of an unannotated `main` waits for step 11, A96), and the refusals
   by exhaustiveness and irredundancy. A test Elm compiles that does not elaborate is a finding
   about the book, the inference, or Elm. Also the refusals that need no
   inference: a lemma that every derivation elaborates every variable, constructor, type
   constructor and qualifier it contains (record labels are not looked up, and operators go through
   OT_stat), so a name that no environment binds has no derivation; and type-expression errors,
   such as a port's payload type that is not `Port(τ)` or an annotated `main` of a wrong type, which
   need only the elaboration of type expressions. The properties and rulings above.
10. **End to end.** Number specialisation and the reductions as Lean functions of the inferred
    derivation; `r:p-program` with both premises, in the test basis; Part I's translations derived in
    Lean. Problem 1 is retired, with problem 11's qualification until step 11.
11. **Complete inference.** Constraint generation and unification with classes and rows, proved
    complete for the rules of Chapters 4 and 5, and principality. Its failure proves the type-error
    tests. Chapter 9's refusals of an undetermined flags type, and the type of an unannotated
    `main` in step 9's legality theorems (A96). Retires problem 11's qualification.

Steps 7 to 10 give most of Part II's value (every compiling test is legal, with the type of an
unannotated `main` qualified until step 11; the trust in the
translator is gone; the refusals without types are proved). Step 11 is the largest step of the
plan, and the only one most of the compile-error tests wait for.

## Findings of Part II

From the second review, before any encoding. For the ambiguity log:

- **Empty types (problem 12; resolved by ruling A97, 2026-11-10).** The book's definition of
  inhabitants made `Never` and `type V = V V` uninhabited. Then `Err e -> never e` on a
  `Result Never Int` broke irredundancy, so the book refused a common idiom Elm accepts; and
  `case m of Nothing -> ...` on a `Maybe Never` was exhaustive, so the book accepted a program Elm
  refuses. The book now reads inhabitants coinductively, so every type has one, as Elm assumes.
- **Defaulting (problem 11).** Restriction 3 should name the principal derivation, and should say
  whether it applies to an annotation's explicit `number` variables.

## Risks

- **Completeness (step 11)** is a research-sized proof. If it stalls, a weaker method serves some
  tests: a per-test unsatisfiable core, a small set of constraints that every derivation must
  satisfy and that unification refutes. This needs completeness of constraint generation only for
  the constructs in the core, but each core is found by hand or by a search.
- **Inference in Lean** duplicates the translator's. That is deliberate (the Lean one is proved,
  and the two are compared), but the comparison will find differences that take time to settle.
- **Build cost.** Elaborating 633 programs adds to a build already near a laptop's memory. Checking
  by `decide +kernel` may be too slow; `native_decide` may be needed.

# Both parts

## Out of scope

Parsing (lexical analysis, layout, the grammar), and so the compile-error tests that elm-syntax
cannot parse; the platform's managers and primitives (Random, Time, Http); libraries outside
elm/core; Appendix E.

## Reviews

### First review, of Part I

An adversarial review (2026-11-10) checked the first draft against the book, the Lean sources, the
translator, the manifest, the tests and the runner. Its corrections, all taken:

- **Tests.** Two of the five `CHECK-NOT` tests are not supported by the book (now "Findings of Part I"),
  and one holds only with the echo host. NonEntryMainEvaluatedOnceTest needs `String.repeat`, so
  group E gains 9, not 10. Two tests that translate today have no meaning in module form.
- **Problem 3.** A soundness theorem that forgets the log cannot support claims about the log;
  replaced by an instrumented relation. The claims about the order of logs (Appendix E leaves only
  independent bindings unordered), their count (thunks re-evaluate; eco evaluates on first use)
  and the runner's matching (substring and regex over stdout and stderr) are corrected.
- **Problem 2.** The description of what the translator does now was wrong. Leaving `main` out
  cannot cover helper modules that call `Html.text`, so the harness basis is needed.
- **Problem 5.** The launcher omits absent flags; it does not pass null. The echo needs both ports.
  Worker tests without ports or flags also run on the native target.
- **Design.** Payload types and boundary values must come before `Val`. Enc, Dec, APPLY and the
  Core relations depend on each other. There is no order on effect values, and the equality
  citation is fixed. The port values and payload types move to step 1. The rulings of Chapter 9
  (A77, A79 to A81) move from step 4 to step 5. Three of the book's properties were missing, and
  one clause of the Enc/Dec property cannot be stated without the static semantics.
- **Other.** Chapter 9 has 20 dynamic rules, not 23. The translator records the lowest-ranked
  refusal, not the first. Cmd.none and Sub.none are not Task texts. The module derived form of
  Appendix A and the thunk translation were missing from the translator's work.

### Second review, of the whole plan

A second adversarial review (2026-11-10) checked the plan with Part II added. Its corrections, all
taken:

- **Tests.** In B0 only 42 of the 633 compile-success tests elaborate: 551 use `Html.text`, which
  Appendix C does not bind, and about 40 use library names. The positive aim is now stated in a
  test basis, and the harness basis of problem 2 is static as well as dynamic, replacing ME0's
  `Html`. The group K classification follows the tests' tags: the lexical and grammar errors are
  out with parsing, and cyclic values, `main`'s recursion, A84 and A89 are syntactic, not type
  errors.
- **Exhaustiveness and irredundancy (problem 12).** The lemma of the draft pointed the wrong way,
  and the book's inhabitants can be empty, which a standard pattern-matrix algorithm does not
  handle. Two findings about the book follow (resolved by ruling A97: inhabitants may be
  infinite, and the standard algorithm applies).
- **Coherence (problem 11).** One derivation fixes one number specialisation, and the book's
  defaulting, read literally, does not pick a unique one. The end-to-end theorem is qualified until
  completeness and principality are proved; two points go to the ambiguity log.
- **Source syntax (problem 8).** Restrictions stated on the source cannot be decided after the
  derived forms, so Lean takes the source syntax and applies the derived forms itself. The
  translator needs a new path for programs it cannot type.
- **Inference (problem 6).** Infer.elm falls short of the rules in many ways (listed), so inference
  is written once in Lean, sound first and complete later, instead of certificates from Infer.elm.
- **Appendix C (problem 10).** The site's data is rendered KaTeX, so an extractor is needed.
- **Other.** Compile-error checks include generic patterns and crash text, not only titles. "Legal"
  needs the restrictions as well as the rules, so the deciders come before the elaboration
  theorems. Missing restrictions, properties and rulings are added. The former step 12 is merged
  into steps 8 and 9, and the intro lists what remains outside Lean more fully.
