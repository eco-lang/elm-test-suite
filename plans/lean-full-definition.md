# Plan: encode the rest of the definition in Lean

**Status (2026-11-11): reviewed three times, lowered to implementation specifications; steps 0
to 3 done (Chapter 7 in Lean, sound and complete, with ME0, the harness, the property of
interfaces and A25; every test translated as the program of modules it is, its checks as
statements about the log; 541 tests); step 4 done (Chapter 8 in Lean, with the round trip
under a named hypothesis about Lean's floats); step 5 done (Chapter 9 in Lean, the 35 worker tests as theorems
about executions, the guarantees of A86 and the rulings; 576 tests); step 6 done (the three
CHECK-NOT lines the book supports, as statements about every execution, by invariants; finding T1
as a theorem; 579 tests); step 7 done (Appendix C extracted, every test classified for the
statics); step 8 done (source and bare syntax, derived forms with the book's choices, the 27
restrictions, theorems for the 916 programs elm-syntax parses); step 9 done (2026-11-12: Chapters 4, 5 and 9's statics, the checker
sound, the pattern decider correct, the test basis; 622 `legal_` theorems under D11, 9 of them by
`native_decide` for the memory budget; 68 `refuse_` theorems, unconditional; see the step's
"Status" for the theorems of its specification proved in another form or not proved); step 10 done (2026-11-12: specialisation, erasure and the pipeline in Lean,
agreeing with the translator on all 579 translated tests; 579 `spec_` and 577 `mean_` theorems;
the rulings; the invariance lemma, `ident_of_spec'`, after ruling A98 and three errata in the
encoding and the book); step 11 under way (milestone (a): 200 of the 217 inference tests refuted
unconditionally, none of the 625 compile-success tests; milestones (b) to (d): W sound, refuting,
complete, principal and terminating at expression level for Hindley–Milner, classes, records and
rows; step 9's checker made exact (canonical rows, no free `bnd`, the erratum on an annotation's
new variables); milestone (e): W with annotations sound, refuting and principal (one clause of
completeness open); milestone (f): module- and program-level W refuting and principal; milestone
(g), 2026-11-13: D11 discharged test by test, `[principal]` retired for every test, 622
`legal_` theorems without hypothesis, all 287 compile-error tests that reach Lean refused, 580
tests end to end (with the two tests of ruling A98, now translated), the general
`PrincipalExistsCore`/`PrincipalExistsMod` proved only from W's coverage; the certificates
then restructured into independent shards by name, `spec_` derived from W's check, built in
15 min by `scripts/verify.sh`; see step 11's "Issues
with the plan", items 10 to 12, for what remains).**

This file is the plan: what is built, in what order, under which decisions, and how
each step is accepted. Each step has an implementation specification in
[lean-full-definition/](lean-full-definition/), which gives the Lean definitions, the theorem
statements, the proof methods, the translator's changes and the acceptance checks of that step.
Where this file and a specification disagree, this file wins and the specification is to be
corrected.

| Step | Specification |
|------|---------------|
| 0 | [step-00-measure.md](lean-full-definition/step-00-measure.md) |
| 1 | [step-01-core-foundations.md](lean-full-definition/step-01-core-foundations.md) |
| 2 | [step-02-modules.md](lean-full-definition/step-02-modules.md) |
| 3 | [step-03-module-form.md](lean-full-definition/step-03-module-form.md) |
| 4 | [step-04-effects.md](lean-full-definition/step-04-effects.md) |
| 5 | [step-05-programs.md](lean-full-definition/step-05-programs.md) |
| 6 | [step-06-every-execution.md](lean-full-definition/step-06-every-execution.md) |
| 7 | [step-07-classify.md](lean-full-definition/step-07-classify.md) |
| 8 | [step-08-source-syntax.md](lean-full-definition/step-08-source-syntax.md) |
| 9 | [step-09-static-semantics.md](lean-full-definition/step-09-static-semantics.md) |
| 10 | [step-10-end-to-end.md](lean-full-definition/step-10-end-to-end.md) |
| 11 | [step-11-complete-inference.md](lean-full-definition/step-11-complete-inference.md) |
| all | [conventions.md](lean-full-definition/conventions.md): file layout, naming, acceptance commands, budgets, reports |

This plan follows phase 6 of [elm-to-lean-translator.md](elm-to-lean-translator.md). The library
values outside the book (`List.map`, `Dict`, ...) are the business of
[core-library.md](core-library.md), which this plan changes in one respect (decision D2).

## What the plan delivers

The Lean mechanisation (`definition/mechanisation/standard-elm-mech`) encodes Chapter 6 (the
dynamic semantics of the Core) and the part of Appendix D that the Core needs. The plan adds the
rest of the book in two parts.

- **Part I, the rest of the dynamic semantics** (steps 0 to 6): Chapter 7 (modules), Chapter 8
  (tasks, commands, subscriptions, ports), Chapter 9's dynamic half (programs and their
  executions), and the whole of Appendix D's dynamic basis for the modules every program imports.
  Every `elm-spec` test that compiles and runs gets theorems about the output it checks, stated
  as the book's evaluation of the whole program (a view) or as an execution the book allows (a
  worker).
- **Part II, the static semantics** (steps 7 to 11): Chapters 4 and 5, Chapter 9's static half,
  Appendix C, the derived forms of Appendix A, and the syntactic restrictions of Chapters 2, 3 and
  9 that can be stated on a syntax tree. Every test that compiles gets a theorem that its program
  elaborates and meets the restrictions; every test that must be refused gets a theorem that it
  is not legal, as far as the method of step 9 or step 11 reaches.

After both parts these stay outside Lean: the concrete syntax (characters, tokens, layout, the
grammar and the resolution of operator fixity), for which the parser elm-syntax stands in; the
values of `Bytes`; the platform's managers (`Random`, `Time`, `Http`); libraries outside the book;
and Appendix E, which records implementations.

## The trust model

A theorem of this mechanisation is about a Lean object that the translator writes. What it
trusts changes as the steps land. Every page that shows a theorem says which of these it relies
on, by the tags in brackets.

| Trusted | Until | Tag |
|---------|-------|-----|
| elm-syntax parses the test as Elm does, and groups its operators by Figure `fig:core-fixities` | always | `[parse]` |
| The translator's elaboration: its number specialisation, its reduced syntax, the port payload types, the order of modules, the type of `main` | retired by step 10 for the 580 tests with an end-to-end theorem (`spec_`) (except that the meaning does not depend on the order of modules, which no step proves) | `[elab]` |
| The harness basis: `Html.text` and the core library's interfaces, which the book does not bind (decision D2) | always (an assumption about the test harness, not about Elm) | `[harness]` |
| The derivation the inference finds for each module of the test's program is principal (`InferPrincipalFor`, decision D11), so "the principal derivation" has a referent | retired by step 11 (2026-11-13) for every test | `[principal]` |
| The Lean compiler, for a theorem proved by `native_decide` | always, for those theorems | `[native]` |
| The implementation parameters: IntRange and norm as eco's (64-bit, wrapping), the empty platform (no managers, primitives or events), and the characters as Lean's `Char` | always (parameters of the definition, fixed by choice) | `[params]` |

`[params]` matters beyond arithmetic: by A31, irredundancy compares integer patterns by their
value as an Int, so whether a match is legal can depend on IntRange (finding B2 below).

## Decisions

These were open in the earlier drafts, and the third review showed that later steps cannot be
specified without them. They bind every specification.

**D1. One evaluator, with an oracle.** The evaluator of `Eval.lean` takes one Boolean `ch` for
every member choice of APPLY, so it does not reach every derivation, and soundness alone cannot
show that a phrase has no value (`Theorems.lean`, comment on `valuesAgree`). Step 1 replaces it
with an evaluator that takes an oracle, a sequence of Booleans (`Nat → Bool`, read at an index
the evaluator threads through) consumed one per choice of APPLY (function equality is the only
APPLY with two members; `Debug.todo` has none), and returns an outcome `value v`, `stuck` (no rule
applies) or `outOfFuel`. Step 1 proves soundness, completeness
(every derivation is found by some oracle and fuel), fuel monotonicity, and oracle independence
when no choice is consulted. A statement "this phrase has no value" (A25, A62, a program with no
meaning, a `CHECK-NOT`) is then proved from completeness: no oracle and fuel give a value. The
existing `#kernel_checks` theorems are re-proved through the new evaluator with the constant
oracles, as one theorem per program (conventions), and the number of checks the kernel proves
must not fall.

**D2. The test basis.** Theorems are stated in the test basis `B_test`, which is `B0` with two
changes, and every theorem names it. (a) The harness: `ME0(Html)`, which the book binds for its
type only, is replaced, statically and dynamically, by an interface that binds
`text : ∀msg. String -> msg Node` and, dynamically, the constructor value `node#` of arity 1,
spelt so that no identifier can name it (as `arr` and `bin` are in Appendix D). This adds no kind
of value and no APPLY case. (b) The core library: the interfaces of [core-library.md](core-library.md)
(`List.map`, `Tuple.first`, ...) extend the interfaces that `B0` already has for those modules
(`List`, `Tuple`, `String`, `Maybe`, `Array` are in `ME0` with their types, and dynamically with
empty or partial interfaces), binding the values of their elm/core texts, and, for a text whose
scheme quantifies a `number` variable (`List.sum`), the value of its copy at `Int` under a new
variable too, as `ME0(Basics)` does for `abs` (Appendix D). They are not added to a program as top-level definitions, as
core-library.md said before: in module form a qualified name resolves through an import's
qualifier, so that device stops working. A lemma of step 2 states that `B_test` agrees with `B0`
on every module but `Html` and the library modules.

**D3. ME0 is complete for the modules every program imports.** Every module begins with the
default imports (Figure `fig:default-imports`), so a derivation for any module reads `ME0` at
`Basics`, `List`, `Maybe`, `Result`, `String`, `Char`, `Tuple`, `Debug`, `Platform`,
`Platform.Cmd` and `Platform.Sub`. Their dynamic interfaces are encoded in full in step 2:
`Ok` and `Err` (until now refused as group B), every Elm text of `Basics` (`logBase` with the
kernel value `Elm.Kernel.Basics.log`, `degrees`, `radians`, `turns`, `fromPolar`, `toPolar`,
`never`), and `Cmd.none`, `Sub.none`, `batch`, `map` and `Platform.worker`, which are effect values
(decision D5). The modules whose dynamic interface the book makes empty (`Array`, `Bytes`, `Json.Encode`,
`Json.Decode`, `VirtualDom`; `Html` is the harness's) are added in step 2 too, since tests import
them; `Task` and `Process` are added in step 4. The payload types (`PTy`), which the reduced
syntax of a port carries, are defined in step 2. A frame lemma (step 2) makes this sound: the
derivation for a module reads the basis only at the modules it imports.

`ME0` is a literal Lean value, with one theorem per Elm text that the rules derive its value
(as `elmTexts_eval` does today for the texts of `Basics`), so no test theorem re-evaluates the
basis in the kernel.

**D4. Logs are a second relation, written once per rule.** `Debug.log` output is outside the
definition (A62), and a `Prop` derivation cannot be inspected, so "the log of a derivation" is
not a Lean term. Step 1 therefore adds, beside each relation of the book, a logged relation with
the same rules and one more index, the log `List (String × Val)`. Each constructor concatenates
the logs of its premises in the order in which the rule writes its premises, and
`r:d-app-basic-apply` at `Debug.log` adds the entry. Two theorems tie it to the book: *forget*
(a logged derivation gives a derivation of the book with the same value) and *lift* (every
derivation of the book has a logged one, with some log). The log is defined by the logged
relation; the book's link to it is the value. The order fixed by "premises in written order" is
one of the orders the book allows (A57, A58: the order of evaluation within a phrase carries no
meaning). It is not Elm/JS's for record fields, which Elm/JS evaluates by field name (Appendix E,
`sec:appendix-implementation-order`). So a check about the order of log lines (`CHECK-NEXT`)
states that the book allows that order, not that it requires it.

Logged relations are added for Chapter 6 in step 1, Chapter 7 in step 2, Chapter 8 in step 4 and
Chapter 9 in step 5, for every relation whose derivations can contain an application of values
(and so a `Debug.log`); a relation that cannot (`Enc`, `Dec`, the merge, exposing lists) has no
logged twin. Their constructor names are the book's rule names with the suffix `_l`
(`r_d_exp_app_l`), and a test in the build checks that each logged relation has exactly the
constructors of its book relation.

**D5. Effect values are constructors of `Val`.** `Val` and `Env` stay a two-type nested mutual
block. Tasks, commands, subscriptions, managers, process identifiers, program values, arrays and
boundary (JSON) values are added as constructors of `Val` (step 2 adds those that `ME0`'s default
modules build, step 4 the rest), so that every structural function on values (`eqSet`, `cmp`,
`showElm`, `recVE`, `isFun`) gains cases but no new mutual type. Arrays are constructor values of
a name `arr#` that no identifier spells (Appendix D, `sec:appendix-dynamic-basis-arrays`).

**D6. Exact numbers.** Lean 4.35's core `Rat` reduces under `decide +kernel` (checked
2026-11-11). Time is `Rat`, a JSON number is a `Rat` (equality of numbers is equality of
rationals, whatever the decimal spelling), and a float delay or a float sent to a port is
converted exactly to `Rat` (every finite binary64 float is a rational). The project stays free of
Mathlib, which would raise the memory floor of every build process.

**D7. JSON objects are canonical.** An object has no order on its keys (A76). Boundary objects
are association lists sorted by key without duplicates, built only through a normalising
function, so that equality of objects is equality of lists, and `Enc` at a record is a function.

**D8. `Enc` and `Dec` are structural functions, with the book's relations beside them.** `APPLY`
reaches `Enc` (an outgoing port), and `Enc` and `Dec` at arrays apply `Array.toList` and
`Array.fromList` (rules `r:e-enc-array`, `r:e-dec-array`). Because those two APPLYs evaluate no
closure (`APPLY(Array.toList, arr# v) = {v}`), `enc` and `dec` are defined by structural recursion
on the payload type, before `Apply.lean`, unfolding those two applications; the book's `Enc` and
`Dec` relations, one constructor per rule, come after `Rules.lean`, and a theorem states
`enc τ v = some j ↔ Enc τ v j`. This keeps `Apply` outside the Core's mutual block.

**D9. Checks are statements about structured logs.** A `CHECK: label: value` line becomes
"the log contains an entry `(label, w)` with `Expect.holds w value`", using the existing `Expect`
(extended to lists, tuples, records and constructor values with arguments, which cover the 158
checks that have no kernel theorem today). Only a check written with `{{regex}}`, a check line with no label (StringEscapesTest), a
`CHECK-SAME` that joins entries, and the pattern of a `CHECK-NOT` (which need not have the form
`label: value`) are compared as printed text, each entry printed as Elm/JS prints `Debug.log`
(`label: ` and the value), by `native_decide`. `CHECK-DAG` is
read as `CHECK`. `CHECK-NEXT` states that two entries are adjacent in the log of the logged
relation's order (each entry prints as one line, since strings are printed with escapes, so this
is the runner's "next line"). `CHECK-NOT` is a universal statement (decision D1, step 6).

**D10. Statics by certificate, completeness later.** The static rules are `Prop` relations, one
constructor per rule, as the dynamic ones. Beside them, step 9 defines *annotated phrases*: the
phrase with a type at each node and an instance at each occurrence of a variable or constructor.
A checker `check : Ctx → AnnPhrase → Bool` is proved sound (`check C a = true` gives a derivation
of `erase a` with the type of `a`) and adequate (every derivation is `check` of some annotated
phrase). An inference written in Lean, *not* proved correct, produces the annotated phrase for
each test, and the test's theorem is `check ... = true`. Instances of derivations, principal
derivations and number specialisation are defined on annotated phrases (Section
`sec:static-core-principal` speaks of nodes of derivations, which a `Prop` cannot expose). Step 11
proves an inference complete and principal, which discharges `[principal]`.

**D11. Legality is conditional until step 11, test by test.** The book defines a legal phrase
by "its principal derivation" (Chapter 4's introduction, A96), and Chapter 9 takes every module
premise from a principal derivation (`programs.tex`, before `r:p-stat-module`). A global
hypothesis that principal derivations exist cannot be used: as the book stands it is false for
modules (finding B6), and a hypothesis that is false makes every theorem under it vacuous. Steps
9 and 10 therefore state their positive theorems under a hypothesis about the test's own program,
`InferPrincipalFor B p`: the derivation that the inference finds for each module of `p`, in the
basis `r:p-stat-module` builds for it, is principal. The further restrictions are proved without
it (decision D12), and so is the type of `main` wherever an annotation or a principality-free
lemma of step 9 fixes it. Step 11 proves `InferPrincipalFor` for every program whose modules are
*coherent* (no type-declaration phrase that `r:sm-topdec-seq` can split with a different result,
finding B6), which covers every test, and removes the hypothesis.

**D12. Exhaustiveness and irredundancy without principality.** A pattern that can fail to match
(a constant, a constructor, `()`, a tuple, `[]`, `::`) fixes the head of its type at its position
in every derivation (rules `r:s-atpat-scon`, `r:s-atpat-con`, `r:s-pat-con`, `r:s-pat-cons` and
the others); every other pattern (wildcard, variable, record pattern) covers everything. So at
every position some pattern examines, all derivations agree on the head and on its constructors,
and the two restrictions are a function of the patterns and the declarations of the custom types
alone; inhabitants (A97: every type has one) only complete counterexamples. Step 9 proves this,
with no reference to principal derivations, and decides the restrictions by a pattern-matrix
algorithm whose constant columns compare constants by denotation (A31: a character by its code,
a string by its characters, an integer by its value as an Int under `norm`).

## Test inventory

From `definition/mechanisation/translation-manifest.json` and the test sources, 2026-11-11: 939
`elm-spec` tests, of which 491 are translated, 311 expect a compile error, and 137 are refused
for another reason. Step 0 regenerates this table by a translator option and replaces it; step 7
does the same for the compile-error tests.

**Part I gains** (tests refused today that the step brings in):

| Step | Tests | Which |
|-----:|------:|-------|
| 2 | 7 | `Ok`/`Err` and `logBase` in `ME0` (D3): CaseFanOutShadowTest, CaseResultTest, ResultErrTest, ResultOkTest, StandardA97NeverErrBranchTest, StandardA97SelfOnlyTypeTest, LetNumberLogBaseTest |
| 3 | 9 | user modules (group G): CompilerIssue2119MutualRecursionUnannotatedTest, CompilerIssue2207MutualRecursionSecondFunctionTest, CovForeignTypesTest, EntryMainOfRootModuleTest, ImportClosedTypeOpenItemTest, ImportExposingAllTest, ImportExposingItemsTest, ImportTypeByNameLaterReplacesTest, StandardA82MainInImportedModuleTest |
| 3 | 5 | record alias constructors: RecordRowsTest, TypeAliasCtorTest, WideRecordDecoder26Test, WideRecordDecoder30Test, WideRecordDecoder70Test |
| 3 | 2 | views whose `main` is not `text "literal"`: HelloTest, CharCasePredicateTest |
| 3 | 15 | port modules whose `main` is a view: the six CovPort* tests and the nine PortEncoding* tests |
| 3 | 9 | log checks (group E): CovEtaDebugLogTest, DebugLogLambdaBoundaryTest, DebugLogRecordTupleFieldTest, DebugNumberAtFloatTest, LetValueBindingTest, PureMutualRecursiveValueTest, PureRecursiveValueThunkTest, StandardA56PrefixAndOrTest, StringEscapesTest (unlabelled) |
| 3 | 2 | regex checks, by `native_decide`: CoreIssue1150CharToCodeLoneSurrogateTest, CoreIssue960PowNegativeExponentIntTest |
| 5 | 34 | workers with positive checks: the 36 `effects` workers (PortEcho*, PortAliasEchoTest, OutgoingPortTuple3*, FlagsRecordTest, StandardA72AbsentFlagsTest, StandardA88PortNegativeZeroTest, CoreIssue1110/1141/1154/955, CmdMapComposeTest, Process*, Task*, TimerEffectTest) less the library tests PortEchoArrayStringTest, PortEchoJsonValueTest and StandardA92BytesPortTest and the size test CoreIssue1123NestedCmdBatchStackOverflowTest; plus NoImportsTest and ListLiteralDebugLogKindTest |
| 5 | 1 | the positive check of StandardA81SleepBeyond32BitsTest (its `CHECK-NOT` is not required by the book, finding T1) |
| 6 | 3 | `CHECK-NOT` workers the book supports: TaskOnErrorSucceedTest (under any host), PortIncomingRejectTest and StandardA88PortNonFiniteTest (with the echo host: another host may send a value whose log contains the pattern) |

Total: up to 87 tests. CompilerIssue2019AliasOfTypeVariableTest (group A, a check the encoding
cannot express) and the library tests (29 `basis:*` beyond step 2's seven, and 5 `import:*`, which
[core-library.md](core-library.md) brings in) are not counted here.

**Part II scope:** the 628 tests that compile (theorems of legality) and the 311 that must be
refused. Measured for step 7's specification (elm-syntax 7.3.9 run over every test, 2026-11-11),
the 311 are: 18 that elm-syntax does not parse; 8 that it parses although they break a rule left
to the parser (`[parse]`); 31 that break a restriction decidable on a syntax tree (step 8); 9
that break exhaustiveness or irredundancy (step 9); 1 whose type error depends on operator
grouping (`[parse]`); and 244 that break a static rule, of which 28 are refused without
inference (unbound names, type expressions, imports and exposing, duplicate ports: step 9) and
216 need step 11. The 628 need, beyond `B0`: nothing, 39; only `Html.text`, 540; library
values, 34; helper modules, 9; modules outside the definition, 3; and 3 do not parse. (Step 7's
classifier, `definition/mechanisation/static-classification.json`, 2026-11-11; it replaces the
regular-expression scan, which counted PortEchoJsonValueTest, a user of `Json.Encode` functions, in
`B0`.)

## Order of work

```
Part I                                    Part II
0  measure                                7  measure, classify, Appendix C extraction
1  Core foundations (D1, D4)              8  source syntax, derived forms, restrictions
2  Chapter 7, ME0 (D3), effect values     9  statics by certificate (D10, D12)
   as data (D5)                           10 end to end, under [principal]
3  module form: translator, every check   11 complete inference, principality
   as a log statement (D9)
4  Chapter 8 (D6, D7, D8)
5  Chapter 9 and the worker tests
6  universal statements (CHECK-NOT)
```

Dependencies ("needs"): 1 needs nothing; 2 needs 1; 3 needs 2; 4 needs 2; 5 needs 3 and 4; 6
needs 5. 7 needs nothing; 8 needs 7; 9 needs 8 and 2 (`ME0` and the harness); 10 needs 9, 3 and
5; 11 needs 9, and its last milestone (removing the hypotheses of step 10's theorems) needs 10. So two tracks can run in parallel from the start (steps 0 to 6, and steps 7 to 9),
with one coordination point: steps 3 and 8 both change the translator (step 3 adds a module-aware
path, step 8 a path that writes the source syntax), and step 8's grouping of a module's
declarations (Appendix A) supersedes step 3's, which is written so that it can be replaced.

Sizes, against the existing mechanisation (about 2,800 lines of Lean) as *large*: step 0 small;
1 medium; 2 large; 3 large (most of it translator work that Part II later replaces); 4 large; 5
large; 6 medium (per-test invariants); 7 small to medium; 8 large; 9 very large; 10 large; 11
research-sized, delivered in milestones (its specification). Step 11's first milestone is the
most valuable: a constraint generator proved complete for derivations, and unification whose
failure is proved to refute every derivation, refuse most type-error tests (about 160 of 216 by
the specification's scan) without completeness of inference, principality or any hypothesis.

## Acceptance of every step

Each specification ends with its own checks. Every step also passes these
([conventions.md](lean-full-definition/conventions.md) gives the exact commands and outputs):

- `lake build` with no `sorry` and no new warnings; `lake exe run-examples` with 0 divergences
  and the number of checks, and of checks proved by the kernel, not lower than before the step
  (a specification may name checks that change, with the reason);
- the translator's unit tests, and `Translate.elm --check` reporting the translations up to date;
- the memory budget: no single Lean process above 6.5 GB, and the whole build under 12 GB of
  proportional set size, measured as the conventions say; a test that breaks it is proved by
  `native_decide` only, or refused, and listed;
- `pnpm test:all` and `node runner/check-baseline.js` unchanged (CI never fails);
- the site data rebuilt, the site built, the link audit at 0 problems, and the rule pages of the
  new rules linking to their Lean constructors;
- the README (Lean section and Files table), `definition/mechanisation/mechanisation-report.md`
  (a dated update), the preface's count of translated tests, and this plan's status line updated.

## Findings

### About the book (for the ambiguity log; none is settled by this plan)

- **B1. Number specialisation starts from an undefined object.** Section
  `sec:dynamic-core-numbers` starts "from the principal derivation of the program", but principal
  derivations are defined for Core phrases and modules only, deliberately not for programs (A96,
  correction 1: a program whose flags nothing fixes has derivations none of which is an instance
  of another). Proposed reading, used by step 10: the sequence of principal derivations of the
  program's modules, each in the basis that `r:p-stat-module` builds from the earlier ones. The
  book should say so, and add that specialisation is invariant under the renamings by which
  principal derivations differ.
- **B2. Irredundancy depends on IntRange and on finite literal domains.** By A31 an integer
  pattern covers the constants with the same value as an Int, so `case n of 0 -> a ; 4294967296
  -> b ; _ -> c` is redundant exactly when `norm(2^32) = 0`; legality depends on an implementation
  parameter. And the clause "no set of special constants covers every inhabitant of Int, Char or
  String" is stated for exhaustiveness only, so a match that lists every Char makes a final `_`
  redundant by the book, though Elm accepts it. The book should either state the clause for both
  restrictions or accept the consequence.
- **B3. The argument for most general unifiers is incomplete.** Section
  `sec:static-core-principal` argues from the meets of the classes alone. A most general solution
  also needs a class pushed into the arguments of a type (a `comparable` variable unified with a
  `List` or a tuple makes its components `comparable`; a `compappend` one with a `List` makes the
  element `comparable`), and a row variable that occurs both alone and extended by a label carries
  an implicit "lacks that label" constraint (the A23 example). Both hold, but the book's sentence
  does not show it. Step 11 proves it.
- **B4. Choices in the derived forms are asserted, not shown, not to matter.** Appendix A numbers
  the components of a `let` and of a module's declarations by any order consistent with their
  dependencies, and says the choice does not matter (A57 to A59). Step 8 fixes one choice and
  states the independence as a lemma for elaboration and evaluation; until it is proved, theorems
  hold for that choice.
- **B5. `r:sm-topdec-types` is a fixed point.** Its type environment occurs on both sides of its
  premises; the book says it is solvable "up to the choice of new type names". Step 9 solves it by
  Appendix A's order of aliases, and step 11's principality of modules needs node correspondence
  for derivations that may also use `r:sm-topdec-seq`.

- **B6. `r:sm-topdec-seq` and `r:sm-topdec-types` disagree.** The comment on
  `r:sm-topdec-types` says that `r:sm-topdec-seq` also applies to a type-declaration phrase,
  splitting it at a separator, and that where both apply "they give the same result". They do not:
  in `type T = T String ; type alias String = Int`, `r:sm-topdec-types` elaborates `T`'s
  constructor with the local alias `String` (so its argument is Int), while splitting first
  elaborates it with the basis's `String`. The two derivations give closed, different types, so
  neither is an instance of the other, and the module has no principal derivation: the property
  of Section `sec:static-modules-principal` is false as stated. Proposed fix: `r:sm-topdec-seq`
  applies only at separators outside a type-declaration phrase. Until the book is fixed, step 11
  proves principality for *coherent* modules (D11), which include every test. **Resolved
  2026-11-12 (ruling A98, option (c)):** the book now has that side condition, which agrees with
  Elm 0.19.1 to 0.19.3 (a module's type declarations are one scope); the Lean checker has no split
  derivation (`r_sm_topdec_seq_types` and `ATopDec.typesSplit` removed), so every module is
  coherent in this sense, and step 11 need not restrict principality to coherent modules on this
  account.
- **B7. Copies in the reduced syntax.** Number specialisation replaces a declaration by copies,
  but the book does not say where the copies stand in the declaration sequence when they refer to
  one another, nor how a destructuring binding is copied (its variables are spelt as labels in a
  record pattern). Step 10 regroups copies by Appendix A's order and states the choice.
- **B8. The instance of a vacuous `number` variable.** By A93 a binding quantifies the `number`
  variables of its group that its own type does not mention, and an occurrence assigns them; no
  sentence of a derivation records that assignment, so the principal derivation does not fix it.
  Section `sec:dynamic-core-numbers` says such a variable "that nothing at the occurrence fixes"
  is Float; step 10 reads every such instance as Float, and the book should say that this is the
  only reading.
- **B9. Two readings for the syntactic restrictions.** Step 8 found two places where the
  restriction's text admits two readings: the scope clause for the variables of a destructuring
  binding, and whether `main` may be declared with parameters. Its specification states the
  reading it encodes for each.

- **B10. Explicit variables cannot be renamed apart.** Section `sec:static-core-principal`
  renames the variables of one derivation apart from the other's, but an explicit type variable
  is named by the syntax, so it is the same in both derivations and the instance substitution
  must fix it. Harmless for the property; the sentence should exempt explicit variables.

### About the existing code

- **C1.** `Basis.lean` and the translator's `Basis.elm` bind `append` in the interface of
  `Basics`. In the book it is hidden: every operator but `::` stands for a variable that `Basics`
  declares but does not expose (Appendix C, `sec:appendix-static-basis-modenv`). Step 2 removes
  it; no test writes `append` unqualified, so no translation changes.

### Not owned by any step

- **Type soundness** of Chapters 6 to 8 (a value of a type is what the type says, so a well-typed
  program's evaluation never meets a value of the wrong form) is a property the book states for
  no chapter, and no step proves it. Step 4's round trip of `Enc` and `Dec` is stated for values
  that `Enc` accepts, which avoids needing it.
- **The order of modules.** Chapter 9 says a program's meaning does not depend on the order in
  which its modules are elaborated and evaluated, where more than one order respects the imports.
  Step 10 retires the trust in the translator's order for the order it chose, not this property.

### About tests

- **T1.** StandardA81SleepBeyond32BitsTest's `CHECK-NOT: the long sleep ended` is not required by
  the book: `r:p-wait` lets 3e9 ms pass and nothing bounds the 200 ms sleep, so the long sleep may
  end, and log, before the kill. Its description should say the `CHECK-NOT` records the
  implementations' behaviour; its translation states its positive check only.
- **T2.** CoreIssue1123NestedCmdBatchStackOverflowTest no longer needs a library function; it
  nests `Cmd.batch` 100,000 deep, which exceeds the evaluator's fuel, and stays out as a size test.

## Issues the specifications raised, and their disposition

Each specification ends with "Issues with the plan". Those that changed this file are folded into
the decisions, the inventory and the findings above (2026-11-11): the oracle as `Nat → Bool`
(D1); one theorem per program, and the count of checks the kernel proves (D1, acceptance); the
library interfaces extending `B0`'s, with copies at `Int` (D2); payload types and the
empty-interface modules in step 2 (D3); no logged twin for a relation that cannot log, such as
`Enc` and `Dec` (D4); unlabelled lines and `CHECK-NOT` patterns compared as printed (D9); the
per-program hypothesis `InferPrincipalFor` (D11, finding B6); the measured counts of steps 0 and 7
(inventory); the echo host for PortIncomingRejectTest (inventory); step 11's last milestone
needing step 10 (order); findings B6 to B10 and C1; conformance out of scope; the two properties
no step owns. The rest are settled inside their specification and need no change here: the
meaning of a check when a label is logged more than once (step 3); the strict tests' two checks
leaving the kernel count (step 3); batch leaves dispatched in reverse order by default, as
Appendix E records for Elm/JS (step 5); the host relation's own state (step 5); boundary values as
one constructor with a well-formedness predicate (step 4); the round trip's one fact about
`Float`, a named hypothesis if it cannot be proved (step 4); certificates in `Certs/` (step 9,
conventions); twenty constructors for Chapter 5's nineteen rules (step 9); a fragment field added
to step 7's classification (step 11).

## Out of scope

Parsing, and so the compile-error tests elm-syntax cannot parse or that are lexical; the
restrictions about characters, tokens and layout (`res:core-escape-unicode`,
`res:core-identifier-characters`, `res:core-constant-separated`, `res:core-adjacent-items`,
`res:core-layout-rule`, `res:core-operator-chain`, `res:core-field-selection`,
`res:core-annotation-placement`, `res:modules-header`); the platform's managers and primitives;
libraries outside elm/core; Appendix E; conformance of an implementation (Chapter 9 defines
it by traces, but it relates the book to an implementation, of which Lean has no model: step 5
defines executions and their traces, and stops there).

## Reviews

### First review, of Part I (2026-11-10)

Corrected the tests (two `CHECK-NOT` tests not supported by the book; group E), problem 3 (a
soundness theorem that forgets the log cannot support claims about it; the order, counting and
matching of logs), problem 2 (the harness basis), problem 5 (the launcher and the echo host), the
design (payload and boundary values before `Val`; Enc, Dec, APPLY and the Core depend on each
other; no order on effect values), and several counts.

### Second review, of the whole plan (2026-11-10)

Added Part II's test basis (in B0 only 42 compile-success tests elaborate), the empty-types
problem (resolved by ruling A97), the coherence problem (resolved by A95 and A96), the source
syntax (restrictions stated before the derived forms), the decision to write inference in Lean,
and the Appendix C extractor.

### Third review, of the whole plan (2026-11-11)

Three independent reviews: Part I against Chapters 7 to 9, the Lean code, the translator and the
runner; Part II against Chapters 2 to 5 and 9 and Appendices A and C; feasibility, with clean
builds measured. 63 findings (3 Blockers, 33 Major) and 34 gaps. The plan was rewritten around
decisions D1 to D12, and lowered into the specifications. The corrections:

- **Blockers.** No module had a derivation without `Ok`/`Err` and the effect values of
  `Cmd.none` in `ME0` (D3, D5). Step 2's checks could not be stated in module form before the log
  existed: the log machinery moved to step 1, and the module form (now step 3) states every check
  once, as a log statement (D4, D9). Legality and `r:p-program` need principal derivations for
  every module, not only for `main` (D11).
- **Proof methods.** Statements that something has no value had no method: the oracle evaluator
  with completeness (D1). "Each log entry is an occurrence in a derivation" is not a Lean
  statement about a `Prop`: the logged relation with forget and lift (D4). The invariance lemma for
  exhaustiveness went through principal derivations: restated without them (D12). The static
  derivations must be inspectable: annotated phrases and a certificate checker (D10). Step 6's
  time abstraction (deadline order) was not sound: per-test invariants instead.
- **Book points**, listed as findings B1 to B5.
- **Facts.** Evaluation order: the book leaves every order within a phrase open, not only
  independent bindings (A57, A58). Test counts restated from the 2026-11-11 manifest (five tests
  named in the earlier draft are now `elm-unspecced`). The memory figure of 6.3 GB is one
  process, nearly all of it one test (AppendTypeSplitTest); the parallel build peaks near 11 GB.
  Nine restrictions cannot be stated on a syntax tree (out of scope). `Enc`, `Dec`, objects and
  numbers need canonical forms (D6, D7). The translator does not yet type modules, ports or
  workers: steps 3 and 5 carry that work explicitly.
- **Renumbering.** Old step 3 (instrumented evaluation) is split: its Core half is the new step 1,
  its use in checks is part of the new step 3. Old step 1 (Chapter 7) is the new step 2; old step
  2 (module form) is the new step 3. Steps 4 to 11 keep their numbers.
