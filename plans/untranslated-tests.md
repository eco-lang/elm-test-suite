# The `elm-spec` tests that do not translate, and what each would need

**Status (2026-11-09): assessment.** After [lean-encoding-widening.md](lean-encoding-widening.md)
steps 1 to 5, 487 of the 941 `elm-spec` tests translate; 454 do not
(`definition/mechanisation/translation-manifest.json`). This file takes each refusal and says
whether the test could be translated, and what it would take. The groups are ordered from the
cheapest to the most expensive.

| Group | Tests | Possible? | What is needed | Size of the work |
|-------|------:|-----------|----------------|------------------|
| A. Test text only | 10 | yes (9 with checks) | exact CHECK lines; `[ -3` spacing | an hour |
| B. Book basis not yet encoded | 6 | yes | `Ok`, `Err` in E0; `logBase` | half a day |
| C. Small translator changes | 9 | yes | `main` body, CHECK-DAG, record alias constructors, record patterns at Float | a day |
| D. elm/core library texts | 28 | yes, by a decision | elm/core's Elm source of Tuple, List, Maybe functions as program text | one to two days |
| E. Debug.log as output | 10 | yes | evaluation with a trace of logged lines | several days |
| F. Implementation-dependent checks | 2 | yes | a directive giving the book's value | an hour, plus the directive |
| G. Modules (Chapter 7) | 9 | yes | user modules: inlining, or Chapter 7 in Lean | days (inlining) to weeks |
| H. Library modules | 5 | no, by design | Array, Dict, Bitwise are not in the book's basis | none |
| I. Size | 7 | not usefully | tests of a compiler's limits | none |
| J. Effects and programs | 60 | yes, large | Chapters 8 and 9 in Lean | weeks |
| K. Compile errors | 308 | partly | the static semantics in Lean, and non-derivability | weeks to months |

## A. Test text only (10)

Each needs an edit to the test, no change to the translator or the encoding.

- **elm-syntax cannot parse `[-n`** (refused `parse`): ContainerCompareIntTest,
  ContainerEqualityFloatTest, ContainerEqualityIntTest. elm-syntax 7.3.9 rejects a negative literal
  right after `[` (`[-3, -2]`: "if a negation sign is not preceded by whitespace, it's considered
  subtraction"), which Elm accepts. Write `[ -3, -2 ]` (elm-format's layout), or work around it in
  the translator by parsing a copy with a space after each `[` (the literal reader takes its text
  from the same copy). Upgrading elm-syntax would also do if a later version fixes it.
- **Unlabelled CHECK lines** (`checks:unlabelled`): CustomTypeMultiFieldTest (`CHECK: person`),
  CustomTypeNestedTest (`nested`), FloatNaNTest (`nanProp`), StringEscapesTest (`newline`, `tab`).
  Replace each with the exact `label: value` line Elm prints.
- **A log without a CHECK line** (`checks:unmatched`): CompilerIssue2019AliasOfTypeVariableTest
  logs `equal` with no CHECK; LetSeparatedStagingTest has no CHECK line at all (its description says
  the result is 18). Add `CHECK: equal: True` and `CHECK: result: 18`, after confirming the values
  with Elm.

CompilerIssue2182ExtensibleFunctionAliasCrashTest (`CHECK: done`) is a compile-success test that
logs nothing: it would translate with no checks, so there is nothing to gain unless a log is added.

## B. The book's basis, not yet encoded (6)

- **`Ok` and `Err`** (`basis:Result.Ok`, `basis:Result.Err`): CaseResultTest,
  LetNumberResultMapTest, ResultOkTest, CaseFanOutShadowTest, ResultErrTest. They are constructors of
  `Result` in Appendices C and D (`appendix-static-basis.tex` 408-412, `appendix-dynamic-basis.tex`
  185, 295), not library functions, so lean-encoding-widening.md's table is wrong to list them as
  library. Add `conOk`, `conErr` and a qualifier `Result` to E0 (as `Just` and `Nothing` are), and
  their schemes to `Translate/Basis.elm`'s `constructor`. LetNumberResultMapTest also uses
  `Result.map`, a library function (group D).
- **`logBase`** (`basis:Basics.logBase`): LetNumberLogBaseTest. An Elm text of the basis
  (`appendix-dynamic-basis.tex` 235) over the kernel's natural logarithm, which the encoding omits.
  Add a hidden basic value `log` (C library, so `native`) and the text, as `abs` is.

## C. Small translator changes (9)

- **`main`'s body is not `text "done"`** (`construct:main-shape`): HelloTest (`text msg`),
  CharCasePredicateTest (`text result`). Accept `text e` for any `e`, keeping `e` out of the
  checks; the main body's value is not observed.
- **CHECK-DAG** (`checks:directive:CHECK-DAG`): ListLiteralDebugLogKindTest. Its logs may come in
  any order; the encoding evaluates each check alone, so CHECK-DAG lines can be read as CHECK
  lines.
- **Record alias constructors** (`construct:record-alias-constructor`): RecordRowsTest,
  TypeAliasCtorTest, WideRecordDecoder26Test, WideRecordDecoder30Test, WideRecordDecoder70Test.
  The alias's constructor is bound by Chapter 7 to a function that builds the record; the
  translator can emit it as a top-level definition (`P = \a b -> { x = a, y = b }`), as it already
  binds custom-type constructors outside the Core. (The Decoder tests import only Html: their
  decoders are the program's own Elm.)
- **A record pattern needed at Float** (`number`): LetNumberRecordDestructureTest
  (`{ lo, hi } = { lo = 30, hi = 40 }` used at Float). A copy cannot rename a record pattern's
  variables, since they are field names. The translator can rewrite a copied record-pattern binding
  as a binding of a fresh variable plus a field access for each name, which the book's derived
  forms allow. Worth checking first whether the book's number specialisation says how such a
  binding is copied: if it does not, that is a finding about the book.

**Update (2026-11-15): settled in the book, by ruling A99 ([record-pattern-rows.md](record-pattern-rows.md)).**
It was a finding about the book: number specialisation asked for a copy no record pattern could
write. The bare pattern row is now `lab = var`, `{ h }` is the derived form of `{ h = h }`, and a
copy renames the row's variable and keeps its label. LetNumberRecordDestructureTest (used only at
Float, the default copy) already translated; CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest
(its record binding used at Int) and the eleven StandardA99RecordPattern*Test programs that compile
are now translated and proved, and the two that Elm rejects (`{ n = m }` and `{ n = n }` written in
a program) are compile-error tests of the new restriction core-pattern-row-label-only. No `elm-spec`
test is refused for `number` any more.

## D. Library functions written in Elm (28)

`basis:Tuple.second` (11), `Tuple.first` (5), `List.map` (3), `List.sum` (2),
`Maybe.withDefault` (2), and one each of `Maybe.andThen`, `Maybe.map`, `List.foldr`, `List.foldl`,
`List.map2`; LetNumberResultMapTest's `Result.map` belongs here too.

The tests: LetNumberTupleSecondTest, RecordNarrow01 to 06, 08 to 10, RecordOpenNarrowFieldIndexTest,
LetNumberAsPatternTest, LetNumberBoxedSilentMiscompileTest, LetNumberContainerDualTest,
LetNumberTupleBothTest, NumberGenericAppTuple, LetNumberListOfClosuresTest,
LetNumberListOfMaybeTest, LetNumberListOfRecordsTest, LetNumberDualUseTest, LetNumberSumMapTest,
NumberGenericAppList, NumberGenericAppMaybe, LetNumberAndThenTest, LetNumberMaybeChainTest,
LetNumberFoldrTest, LetNumberIndirectFoldlTest, LetNumberMap2Test.

These functions are library, outside the book. But nearly all the tests are about the language,
mostly number specialisation (`LetNumber*`, `NumberGeneric*`) and record narrowing, and they use
the library only incidentally. All these functions but `List.map2` are plain Elm in elm/core 1.0.5,
`List.foldr` included (its helper is Elm); `List.map2` is `Elm.Kernel.List.map2`. So the translator could add the elm/core text of each function a
test uses as a top-level definition of the program, under its qualified name, and specialise it
like the program's own code. `List.sum : List number -> number` then gets its copy at Float, which
is what these tests exercise. The decision: whether the mechanisation may check a test against
the book plus elm/core's Elm text. That text would be marked as library on the test's page.
[core-library.md](core-library.md) proposes this, with a Core Library section of the site that
specifies elm/core against the book.

**Update (2026-11-13): 28 of the 29 translated** ([library-elm-texts.md](library-elm-texts.md)).
Not as top-level definitions of each program, but as values of the dynamic test basis
(`Lib.Btest`): the translator writes the closure of elm/core 1.0.5's texts of `List.foldl`,
`foldr`, `head`, `length`, `map`, `sum`, `Maybe.andThen`, `map`, `withDefault`, `Result.map`,
`Tuple.first` and `second` as four library modules (`Generated/Library.lean`), and Lean evaluates
them by Chapter 7's rules. Every test of this group but LetNumberMap2Test now has `t_`, `spec_`,
`ident_` and `mean_` theorems, tagged `[library]`; 18 are `[native]` because they use `round`
(none for the memory budget). LetNumberMap2Test stays out: `List.map2` is a kernel value.

**Update (2026-11-14): LetNumberMap2Test is no longer `elm-spec`.** It keeps `List.map2` as a
test of a `number` literal crossing a kernel function, untagged; `LetNumberLocalMap2Test`, new and
`elm-spec`, checks the same typing with a `map2` written in the program, and is translated and
proved.

## E. Debug.log as observable output (10)

`checks:unmatched` (9): DebugLogLambdaBoundaryTest, DebugNumberAtFloatTest, CovEtaDebugLogTest,
LetValueBindingTest, PureMutualRecursiveValueTest, PureRecursiveValueThunkTest,
StandardA56PrefixAndOrTest, StandardA87NumberDefaultCopyTest, DebugLogRecordTupleFieldTest; and
CHECK-NEXT: NonEntryMainEvaluatedOnceTest. These check lines that `Debug.log` prints from inside
expressions: whether, how often and in what order a log runs (A56's short circuit, A87's default
copy being evaluated, a value evaluated once). The encoding has `Debug.log` return its value and
records no output. Needed: an evaluation that also yields the sequence of logged lines (in the
book's terms, the observable output of evaluating a program's top level). The translator would then
turn every CHECK, CHECK-NEXT and CHECK-NOT line into a statement about that sequence. This is the
most valuable of the mid-sized steps: these tests are about evaluation order and sharing, which
the current checks cannot see. Where the book leaves an order of evaluation open,
the statement would have to allow each order it permits.
NonEntryMainEvaluatedOnceTest also needs `String.repeat` (in its helper NonEntryMainAux), a
library function, so it waits for [core-library.md](core-library.md) as well. The plan for this
group is step 3 of [lean-full-definition.md](lean-full-definition.md).

## F. Implementation-dependent checks (2)

`checks:regex`: CoreIssue1150CharToCodeLoneSurrogateTest (`Char.toCode` of a lone surrogate),
CoreIssue960PowNegativeExponentIntTest (Int `^` with a negative exponent). The CHECK lines are
regular expressions because implementations differ. The book gives one value: A43 for `^`, and the
Char model's `other(n)` for the surrogate. A directive such as `-- DEFINITION: pow: 0` stating the
book's value would let the translator check it. Both values are in the encoding already.

## G. User modules (9)

`import:ModuleExposingHelper` (ImportClosedTypeOpenItemTest, ImportExposingAllTest,
ImportExposingItemsTest), `import:CompilerIssue2119View`, `import:CompilerIssue2207Mutual`,
`import:CovForeignTypesHelper`, `import:EntryAuxWithMain`, `import:ImportTypeByNameFirstHelper`,
`import:StandardA82MainHelper`. The helpers are in `tests/elm/src/`. Two ways:

1. The translator resolves the imports and inlines the helpers' declarations, qualified. It is
   cheap, but it checks only the Core and leaves out exposing and import rules, which is what most
   of these tests are about.
2. Chapter 7's dynamic semantics (module environments, `QE`, exposing) is encoded in Lean and the
   programs are translated as module sequences. This is the real step, and it also brings in
   record alias constructors properly (group C). This is the way chosen: step 1 of
   [lean-full-definition.md](lean-full-definition.md).

## H. Library modules (5): stay out

`import:Array` (ArrayAppendCanonicalTest, ArrayEqAfterPushTest, LetNumberArrayMapTest),
`import:Dict` (DictMapStagedCaptureTest), `import:Bitwise`
(FunctionValuesChosenByIfCaseAndTupleTest). Array is in ME0 only as library, and Dict and Bitwise
are not in it (Appendix C). FunctionValuesChosenByIfCaseAndTupleTest might be rewritten without
Bitwise, if Bitwise is incidental to it.

**Update (2026-11-14): none of the five is an untranslated `elm-spec` test now.** Each test was
asked what in the book it checks, and whether it could check that within the basis:
- FunctionValuesChosenByIfCaseAndTupleTest: Bitwise, Bytes.Decode and Bytes.Encode were unused
  imports; they are removed, and the test is translated and proved.
- DictMapStagedCaptureTest: it checks a staged application inside a two-argument lambda, which
  needs no `Dict`. The dictionary is now a list of pairs with a `mapValues` written in the program,
  and `String.length` is replaced by an Int; translated and proved.
- ArrayAppendCanonicalTest, ArrayEqAfterPushTest, LetNumberArrayMapTest: within the basis an array
  reaches a program only through its flags or a port, so arrays of different construction cannot
  be compared, and the `number` typing is checked by the `LetNumber` tests over lists. They are
  tagged `elm-unspecced` instead, without book tags. `ArrayEqualityFlagsTest`, new and
  `elm-spec`, checks the equality of arrays with arrays received as flags (`b:Basics.eq`,
  `b:Array.Array`, `fig:dynamic-basis-eq`); `b:Array.Array` is also named by
  `CovPortIncomingArrayTest` and `PortEncodingPortWithArrayTest`, which declare ports of arrays.

PortEchoArrayStringTest (group J) built its arrays with `Array.empty` and
`Array.fromList`; it stays as an untagged test that needs only the port echo, and
`PortEchoArrayStringFlagsTest`, new and `elm-spec`, sends arrays received as flags.

## I. Size (7): not usefully

`construct:large-program` (CompilerIssue2281LongLineListTest, WideClosureArity300Test,
WideRecord1100Test, WideRecord600Test, WideRecordDecoder300Test), `construct:large-computation`
(WideRecordGcBitmapTest), `construct:large-type` (EtaExpandSeventeenArgumentAliasTest). These test a
compiler's limits (records of 1100 fields, 300-argument closures, lists of 150000 elements, a
type of hundreds of arrows). Lean could take some of them with more fuel and recursion depth, at a
large cost in build time and memory, and they say little about the semantics.

**Update (2026-11-15): none of them is `elm-spec` now.** The book places no bound on the size of a
phrase or on the resources evaluation uses, and Appendix "Implementation-Dependent Details",
"Resource Limits", lists the limits of each implementation: a compiler that rejects one of these
programs for its size, or stops for lack of stack or memory, does not contradict the book. So
WideClosureArity300Test, WideRecord1100Test, WideRecord600Test, WideRecordDecoder300Test,
WideRecordGcBitmapTest, EtaExpandSeventeenArgumentAliasTest and
CoreIssue1123NestedCmdBatchStackOverflowTest (group J, the `Cmd.batch` nested 100000 deep) are
tagged `elm-unspecced`, with no rule tags, and each says why in its comment; CoreIssue1123 keeps
`elm19-bug`. CompilerIssue2281LongLineListTest (a line
of 66000 columns), already not `elm-spec`, is tagged `elm-unspecced` too and keeps `elm19-bug-fix`.

## J. Effects and programs (60)

`effects` (54): 37 port modules (16 of them import Json modules, but only PortEchoJsonValueTest
calls a Json function), 21 tests using
Task or Process (some of them port modules too), Platform.worker programs, Random (1). In addition: `checks:check-not`
(PortIncomingRejectTest, ProcessKillRunnableTest, StandardA81SleepBeyond32BitsTest,
TaskOnErrorSucceedTest), CHECK-NEXT StandardA88PortNonFiniteTest, and NoImportsTest
(`construct:main-shape`: a `Platform.worker` whose `init` logs).

Needed: Chapters 8 and 9 in Lean (programs, the effect managers, the scheduler and its
nondeterminism, ports as input and output) and a model of the test harness's flags and incoming
port values. PortEchoJsonValueTest also needs `Json.Encode.encode`, a library function outside
elm/core. Possible, but a project the size of the current mechanisation.
[lean-full-definition.md](lean-full-definition.md) (Part I) plans it. Two of the `CHECK-NOT` tests,
ProcessKillRunnableTest and StandardA81SleepBeyond32BitsTest, check more than the book requires:
the book allows the line they forbid (that plan, "Findings of Part I").

**Update (2026-11-14): the two port tests that called library functions.** PortEchoJsonValueTest
now takes its Values as flags at `Json.Encode.Value` (`e-dec-value`), sends them out as they are
(`e-enc-value`), and logs them as they come back decoded at a record, a string and a pair; Elm
prints a Value as `<internals>`, so a Value cannot be logged itself. It is translated and proved.
StandardA92BytesPortTest stays `elm-spec` and untranslated, as the only test of `e-enc-bytes` and
`e-dec-bytes`: within the basis no program can make a `Bytes` value. The new
StandardA92BytesPortDeclarationTest checks the static half of ruling A92 (`Port(Bytes)`, with
`b:Bytes.Bytes`) and is translated and proved; Elm 0.19.1 to 0.19.3 reject it, and Lamdera 1.5.0
accepts it.

**Update (2026-11-15): pipe tests ([host-pipe-tests.md](host-pipe-tests.md)).** The test driver
can now send boundary values in on a port (`-- HOST-SEND:`) and check what the program sends out
(`<port> sent:` CHECK lines), and Lean's `Host.feed` models it. Ten `PortPipe*Test`s check the
Encoding and Decoding rules this way, `e-dec-bytes` and `e-enc-bytes` among them, with byte
sequences the driver sends, and all ten are translated and proved. StandardA92BytesPortTest, which
built its bytes with elm/bytes, is deleted: PortPipeBytesTest checks the round trip within the
basis, and StandardA92BytesPortDeclarationTest the declarations.

## K. Compile errors (308)

Every one expects the compiler to refuse the program. By the book's layers (from their tags):
about 216 cite the static semantics of the Core (type errors, annotations too general, record
extension, infinite types, cyclic values), 50 the module level (headers, exposing, imports, aliases,
`main`'s type), 36 the syntax and its restrictions (layout, escapes, operator chains,
exhaustiveness, redundancy, shadowing), and 6 others. 216 are also tagged `elm19-compile-error`
(many check that Elm gives an error rather than crashing or hanging).

A translation would state that *no* derivation exists, which is harder than the current theorems:

1. **Restrictions** (most of the 36): decidable predicates over the syntax (shadowing,
   exhaustiveness, redundancy, distinct names). They could be encoded and decided per test. This
   is the cheapest part. The lexical ones (bad escapes, layout) would need lexing and parsing in
   Lean, or trust in the translator's parser.
2. **Typing** (about 216): the static semantics of Chapters 4 and 5 in Lean, and either an
   inference algorithm proved *complete* with respect to the rules (so that its failure proves
   untypability), or a proof per test. Completeness for Elm's classes, records with rows, and
   number defaulting is a substantial piece of work. Soundness alone (the evaluator's direction)
   would not do.
3. **Modules** (50): the static semantics of Chapter 7 on top of 2.

The static semantics is also what would let the mechanisation check the translator's own type
inference, which number specialisation now trusts. Part II of
[lean-full-definition.md](lean-full-definition.md) plans both.

## Suggested order

A and B first (15 tests with checks, little work), then C (9), E (12, and the most informative), D after a
decision on library text, G by inlining if the tests' import rules can wait, then the large
steps G, J and K, which [lean-full-definition.md](lean-full-definition.md) plans.
