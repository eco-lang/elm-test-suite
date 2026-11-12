# Step 7: measure, classify, extract Appendix C

Part of [the plan](../lean-full-definition.md), Part II. Follows
[conventions.md](conventions.md). Status: specified 2026-11-11, not started.

## Goal

Step 7 writes no Lean. It produces the data that steps 8 to 11 are measured against and built
from:

1. **A classification of every `elm-spec` test for the static semantics**, written by the
   translator to `definition/mechanisation/static-classification.json`: for each of the 311
   compile-error tests, whether elm-syntax parses it (with its helper modules), the rule or
   restriction of the book it breaks, and the class of proof that will refuse it (and in which
   step); for each of the 628 compile-success tests, what it needs beyond the book's basis `B0`
   (the harness, core library values, helper modules, modules outside the definition).
2. **An extraction of Appendix C** (`definition/tex/appendix-static-basis.tex`) and of
   Figure `fig:default-imports` (`definition/tex/syntax-modules.tex`) into
   `definition/mechanisation/static-basis.json`, covering every row shape of the appendix, from
   which step 9 generates the static `ME0` in Lean.
3. **A check of `definition/tools/src/Translate/Basis.elm`** (the translator's hand-written type
   schemes) against that extraction.
4. **A decision on "parses it as Elm does"** (gap G2-16): dropped as a check, kept as the `[parse]`
   trust, with the tests where elm-syntax is known to read a text Elm refuses listed by name.

This replaces the plan's provisional Part II counts by measured ones, as the plan's "Test
inventory" requires ("step 7 does the same for the compile-error tests").

## Prerequisites

- None from Part I: step 7 needs nothing (plan, "Order of work").
- Tools as [conventions.md](conventions.md) gives them: elm-pages from `site/node_modules`,
  elm-syntax 7.3.9 (`definition/tools/elm.json`), the translator's `Translate.Directives.read`
  (selection of `elm-spec` tests: every `-- TAGS:` line concatenated, `elm-spec` among the tags,
  no `-- HELPER:` line; compile error: a `-- COMPILE-ERROR:` line).
- If step 0 has landed, its option `--report-all-refusals` is left as it is; step 7's option is
  independent of it.

## Lean definitions

None. Step 7 changes no Lean file and no Generated file other than the two JSON files below.

## Theorems

None.

## Translator changes

### 1. Files

| File | New or changed | Contents |
|------|----------------|----------|
| `definition/tools/src/ExtractStaticBasis.elm` | new | elm-pages script: reads the two `.tex` files, writes `static-basis.json`; `--check` compares; runs the Basis.elm check (section 6) |
| `definition/tools/src/StaticBasis/Latex.elm` | new | pure functions: tokenising a LaTeX array, joining continuation rows, parsing a scheme (section 4) |
| `definition/tools/src/StaticBasis/Json.elm` | new | the JSON encoders and decoders of section 5 (the decoder is used by the classifier and by step 9's Lean writer) |
| `definition/tools/src/Translate/Classify.elm` | new | pure: the classification of one test (sections 2 and 3) |
| `definition/tools/src/Translate/ClassifyOverrides.elm` | new | the hand-reviewed table of section 2.4 |
| `definition/tools/src/Translate/Basis.elm` | changed | one export, `valueNames` (section 6) |
| `definition/tools/src/Translate.elm` | changed | reads helper modules, `static-basis.json` and the book's labels; writes `static-classification.json` on every run; option `--classify-static` |
| `definition/tools/tests/StaticBasisTest.elm` | new | unit tests of `StaticBasis.Latex` (section 7) |
| `definition/tools/tests/ClassifyTest.elm` | new | unit tests of `Translate.Classify` (section 7) |

`ExtractStaticBasis.elm` runs before the translator (the classifier reads its output). Both are
run from the repository root:

```
site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm
site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm --check
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --classify-static
```

`--classify-static` writes nothing: it prints the summary of section 3.3 and the list of tests per
class, for review. The normal run writes `static-classification.json` with the other outputs,
and `--check` compares it like the others (it is added to `outputs` in `Translate.elm`).

### 2. The classification of the 311 compile-error tests

#### 2.1 The program of a test

A test's *modules* are the test file and, transitively, every module it imports that is a file
`tests/<project>/src/<M with dots as slashes>.elm` (a *helper*; it need not carry `-- HELPER:`:
`ModuleHeaderMissingHelper.elm` has none). Each module is parsed with `Elm.Parser.parseToFile`.
The program *parses* when every module does. A cycle of imports among helpers is followed once
(a visited set), so `ImportCycleTest` has the three modules `ImportCycleA`, `ImportCycleB`,
`ImportCycleTest`.

#### 2.2 The book labels of a test

The book's labels are read from `definition/tex/*.tex`: every argument of `\label{...}`,
`\citelabel{...}`, `\citealso{...}`, and every `\defnrule[...]` label. A tag `t` of a test
*resolves* to the first of `r:t`, `res:t`, `t` that is a label. The test's `rules` are its
resolved tags in the order written; its `rule` is the first of them, unless the override table
(2.4) gives another. Measured 2026-11-11: every one of the 311 compile-error tests has at least
one resolved tag; the unresolved tags are only `elm-spec`, `elm19-compile-error`, `elm19-bug`
and `elm19-bug-fix`.

#### 2.3 The classes

Every compile-error test gets exactly one class, by the first rule below that applies. The
*trusted restrictions* are the nine the plan puts out of scope (plan, "Out of scope"):
`res:core-escape-unicode`, `res:core-identifier-characters`, `res:core-constant-separated`,
`res:core-adjacent-items`, `res:core-layout-rule`, `res:core-operator-chain`,
`res:core-field-selection`, `res:core-annotation-placement`, `res:modules-header`.

| Class | Rule | Proved by | Trust |
|-------|------|-----------|-------|
| `parse-fail` | some module of the program does not parse | out (no syntax tree) | |
| `lexical-accepted` | it parses, and its `rule` is a trusted restriction | out: elm-syntax reads a text Elm refuses, so a theorem about the tree would be about another program | |
| `syntactic` | its `rule` is one of the 27 AST-decidable restrictions listed in [step 8](step-08-source-syntax.md) | step 8 | `[parse]` |
| `further` | its `rule` is `res:core-exhaustiveness` or `res:core-irredundancy` | step 9 (decision D12; no principality needed) | `[parse]`, `[params]` |
| `fixity-inference` | its `rule` is `fig:core-fixities` | step 11 | `[parse]` (the grouping) |
| `static-deterministic` | the override table says so (2.4) | step 9, without inference | `[parse]`, `[harness]` |
| `inference` | otherwise (a static rule `r:s-*`, `r:sm-*`, `r:p-*` whose refusal needs complete inference) | step 11 | `[parse]`, `[harness]` |

`static-deterministic` has a subclass, one of `scope` (a name that no environment of any
derivation binds), `type-expression` (a type expression, of an annotation, a declaration or a
port, that elaborates in no context the rules can build), `module` (imports, exposing lists, the
header, a port's payload type, the names of ports), `main` (the type of `main` is fixed by its
annotation, or its head by its expression, and is wrong), `arity` (a constructor pattern with the
wrong number of arguments). These are the families of P2-13 that step 9 refuses with the lemmas
of its section "Refusals without inference".

#### 2.4 The override table

`Translate/ClassifyOverrides.elm` is the one hand edit surface of the classification:

```elm
module Translate.ClassifyOverrides exposing (Override, overrides)

type alias Override =
    { name : String              -- the test's name, e.g. "BadMainTypeUnitMainTest"
    , rule : Maybe String        -- a book label replacing the first resolved tag, if any
    , class : String             -- one of the classes of 2.3
    , subclass : Maybe String    -- for static-deterministic
    , note : String              -- one sentence: why, for the reader of the JSON
    }

overrides : List Override
```

Procedure, done once in step 7 and kept up to date by steps 8, 9 and 11: every test whose
automatic class (2.3 without the table) is `inference` is read by hand, from its source, its
`-- COMPILE-ERROR:` text and its first `CHECK` title, and either left as `inference` or given an
override. An override is also used where the first tag is not the restriction actually broken
(for example a test tagged `res:modules-alias-not-recursive` whose program breaks no cycle but a
qualified self-reference). When a later step cannot prove a test in its class, that step changes
the override and says so in its report.

Provisional hand review, from the tags and titles (2026-11-11), to be confirmed by reading each
test:

| Subclass | Tests (first tag) | Count |
|----------|-------------------|------:|
| `scope` | NamingErrorAnUnknownVariableTest (`r:s-atexp-longvar`) | 1 |
| `type-expression` | the twelve `r:s-ty-con` tests (CompilerIssue1550RecordExtensionDuplicateFieldTest, CompilerIssue1785ExtensibleAliasOfUnitTest, CompilerIssue1896ExtendCustomTypeCrashTest, CompilerIssue1952ExtendIntCrashTest, CompilerIssue2064ExtendStringNotEnoughBytesTest, CompilerIssue2072ExtendUnitInResultCrashTest, CompilerIssue2083ExtendCustomTypeFieldAccessCrashTest, CompilerIssue2097ExtensibleUnitArgCrashTest, CompilerIssue2176ExtensibleUnitAliasCrashTest, CompilerIssue2182ExtensibleFunctionAliasCrashTest, QualifiedTypeNotExposedTest, TypeConstructorTooFewArgsTest) and the `r:s-ty-openrecord` test | 13 |
| `module` | ImportAliasOpenItemTest, ImportClosedTypeConstructorTest, ImportUnexposedValueTest, ImportUnknownOperatorTest, PortProblemCharPayloadTest, StandardA84DuplicatePortNameTest | 6 |
| `main` | BadMainTypeAliasMainTest, BadMainTypeFunctionMainTest, BadMainTypeRecordMainTest, BadMainTypeThreeArgumentTypeMainTest, BadMainTypeUnitMainTest (annotated), BadMainTypeTypeVariableMainTest (`main = []`, head `List` in every derivation) | 6 |
| `arity` | TooFewArgsAConstructorPatternWithTooFewArgumentsTest, TooManyArgsAConstructorPatternWithTooManyArgumentsTest | 2 |
| total `static-deterministic` | | 28 |

The other 216 static-rule tests stay `inference`, StandardA96NumberFlagsTest among them (an
unannotated `main` whose flags type only the principal derivation decides).

#### 2.5 Measured parse status and the classes that do not depend on the review

Measured 2026-11-11 with elm-syntax 7.3.9 (a scratch copy of the translator; numbers exact):

- **`parse-fail`, 18**: BadTupleATupleOfFourTest, InfixNoQualifiedOperatorTest,
  InfixNoSectionLeftTest, InfixNoSectionRightTest (`fig:core-grammar-expressions`);
  ParseErrorCasePatternUnfinishedTest (`fig:core-grammar-patterns`); TypeExprUnitAppliedTest
  (`fig:core-grammar-types`); PortProblemDeclarationWithoutNameTest
  (`fig:grammar-top-level-declarations`); UnknownOperatorAnUnknownOperatorTest (`r:s-atexp-op`);
  AnnotationNotFollowedByDefinitionTest (`res:core-annotation-placement`);
  ParseErrorStringEscapeUnclosedTest (`res:core-escape-unicode`);
  WeirdElseBranchElseNotIndentedTest (`res:core-layout-rule`);
  UnexpectedPatternFloatWithExponentTest (`res:core-no-float-pattern`); InfixNonAssocCompareTest,
  InfixNonAssocEqTwiceTest (`res:core-operator-chain`); RecordUpdateNoFieldsTest
  (`res:core-record-update-form`); ImportAliasQualifiedTest (`res:modules-import-alias`);
  TopLevelPatternBindingTest (`res:modules-no-top-pattern`); ModuleHeaderMissingImportedTest (its
  helper `ModuleHeaderMissingHelper.elm` has no header and does not parse; the test file itself
  parses).
- **`lexical-accepted`, 8**: StandardA1UnitPatternGapTest (`( )` read as `()`),
  ParseErrorNumberBadHexDigitTest (`0x1g` read as `0x1 g`), ParseErrorNumberFractionThenLetterTest
  (`1.5a` read as `1.5 a`), CharLiteralSurrogateEscapeTest, ParseErrorStringEscapeTooFewDigitsTest,
  StandardA8SurrogateEscapeTest (escapes Elm rejects), InfixMixedAssocComposeTest,
  InfixMixedAssocPipesTest (chains Elm rejects, which elm-syntax groups).
- **`syntactic`, 31**: NameClashTwoArgumentsOfOneNameTest, NameClashTwoLetBindingsOfOneNameTest
  (`res:core-binding-site-distinct`); CyclicValueALetValueDefinedByItselfTest,
  LetCycleThroughRecordLambdaTest (`res:core-let-recursion`); ShadowingShadowingInLambdaTest
  (`res:core-no-shadowing`); NameClashARecordFieldGivenTwiceTest (`res:core-row-labels-distinct`);
  AliasProblemExtensibleRecordUnitTupleAndFunctionTest, AliasProblemQualifiedTypeTest,
  AliasProblemRecursiveAliasWithCommentedParensTest (`res:modules-alias-not-recursive`);
  AliasUnboundVariableTest, AliasUnusedParameterTest (`res:modules-alias-tyvars`);
  StandardA91BasicsAliasTest (`res:modules-basics-qualifier`); TopLevelConstructorTwiceTest,
  TopLevelRecordAliasConstructorClashTest (`res:modules-constructors-distinct`);
  CustomTypeUnboundRowVariableTest, CustomTypeUnboundVariableTest
  (`res:modules-custom-type-tyvars`); HeaderExposesTwiceTest, HeaderExposesTypeTwiceTest
  (`res:modules-exposing-distinct`); HeaderExposesAliasOpenTest,
  HeaderExposesConstructorByNameTest, HeaderExposesUndeclaredValueTest
  (`res:modules-header-exposing`); HeaderExposesOperatorTest (`res:modules-no-operator-exposing`);
  ShadowingAnArgumentShadowingATopLevelValueTest (`res:modules-no-shadowing`);
  TopLevelTypeAndAliasSameNameTest (`res:modules-types-distinct`); TypeParameterTwiceTest
  (`res:modules-tyvarseq-distinct`); CyclicDefinitionATopLevelValueDefinedByItselfTest
  (`res:modules-value-recursion`); TopLevelPortAndValueSameNameTest, TopLevelValueTwiceTest
  (`res:modules-values-distinct`); ImportCycleTest (`res:program-import-order`);
  BadMainRecursiveMainTest, BadMainRecursiveUnannotatedMainTest (`res:program-main`).
  (The plan's "37" counted `res:core-annotation-placement` and `res:modules-header`, which are
  trusted, and four tests that do not parse.)
- **`further`, 9**: MissingPatternsAMissingListLengthTest, MissingPatternsAMissingTupleShapeTest,
  StandardA97MaybeNeverMissingJustTest, UnsafePatternAllDestructPatternsEdgeCaseCasesTest,
  UnsafePatternDestructFixedListPatternLetDestructCasesTest,
  UnsafePatternMixedNestedAliasesAsPatternCasesTest,
  UnsafePatternTripleNestedPatternsPatternArgCasesTest (exhaustiveness, 7);
  CaseCharEscapedDuplicateTest, RedundantPatternABranchAfterAWildcardTest (irredundancy, 2).
- **`fixity-inference`, 1**: InfixAssocRightConsAppendTest.
- **static rules, 244**: the rest; split by 2.4 into `static-deterministic` (provisionally 28)
  and `inference` (provisionally 216).

All 311 are in project `elm`.

#### 2.6 "Parses it as Elm does" (G2-16): dropped as a check

No parser that is known to agree with Elm is available to compare with (Elm's own parser does not
expose its tree, and eco's would be a third reading to trust). Re-printing the elm-syntax tree and
comparing it with the source up to layout would test elm-syntax against its own printer, not
against Elm. So step 7 does not check the clause. It stays the `[parse]` trust of the plan, which
every Part II theorem names, and step 7 records the evidence against it that exists:

- the 8 `lexical-accepted` tests (elm-syntax reads a text that Elm refuses lexically);
- the 3 compile-success tests elm-syntax cannot parse (ContainerCompareIntTest,
  ContainerEqualityFloatTest, ContainerEqualityIntTest: `[-3`), refused today with reason
  `parse`;
- for operator grouping, the one `fixity-inference` test, whose refusal depends on the grouping
  elm-syntax chose; its theorem (step 11) is marked `[parse]` like every other, and its page says
  that the grouping is the point of the test.

The JSON field `"parse"` is therefore `"ok"` or `"fail"` only; there is no `"asElm"` field.

### 3. The recount of the 628 compile-success tests

#### 3.1 What each test needs

For each compile-success test whose program parses, the classifier resolves every reference of
every module by the imports as Chapter 5 reads them (default imports first, Figure
`fig:default-imports`; `as` qualifiers; `exposing` items and `(..)`), against the static basis of
`static-basis.json`, and records:

- `helper:<M>` for each helper module of the program;
- `harness` if some module uses `Html.text` (qualified, or exposed by `import Html exposing
  (text)` or `(..)`), the value D2 adds;
- `library:<M>.<x>` for each value, constructor or type constructor referred to in a module of
  `ME0` that `static-basis.json` does not bind in that module's interface (`List.map`,
  `Tuple.first`, `String.length`, `Array.fromList`, ...), and for each such name an import
  exposes;
- `outside:<M>` for each imported module that is neither in `Dom ME0` nor a helper (`Dict`,
  `Bitwise`, `Bytes.Encode`, `Bytes.Decode`, ...).

Its `basis` is then the first that applies of: `parse-fail`; `outside` (some `outside:`);
`helper` (some `helper:`); `library` (some `library:`); `harness`; `B0`. The record also has
`main`: `"view"`, `"program"` or `"other"` from the syntactic shape (an application spine of
`text`/`Html.text`, or of `Platform.worker`), and `mainAnnotated`: whether the main module's
`main` has an annotation. Step 9 uses both to plan its main-type lemmas.

#### 3.2 Expected numbers

A regular-expression scan made for this specification (2026-11-11) gives the following; the
classifier, which resolves names by the imports, replaces it, and the step's report explains
every difference:

| `basis` | Tests | Which |
|---------|------:|-------|
| `B0` | 40 | NoImportsTest, ListLiteralDebugLogKindTest, CmdMapComposeTest and the 37 worker and port tests of `effects`/`check-not` that import no `Html` (PortEcho\*, Process\*, Task\*, CoreIssue1110/1123/1141/1154/955, FlagsRecordTest, OutgoingPortTuple3\*, PortAliasEchoTest, PortIncomingRejectTest, StandardA72AbsentFlagsTest, StandardA81SleepBeyond32BitsTest, StandardA88PortNegativeZeroTest, StandardA88PortNonFiniteTest, TimerEffectTest) |
| `harness` | 540 | import `Html`, use only `Html.text` beyond `B0` |
| `library` | 33 | ArrayAppendCanonicalTest, ArrayEqAfterPushTest, the 17 `LetNumber*` library tests (AndThen, ArrayMap, AsPattern, BoxedSilentMiscompile, ContainerDual, DualUse, Foldr, IndirectFoldl, ListOfClosures, ListOfMaybe, ListOfRecords, Map2, MaybeChain, ResultMap, SumMap, TupleBoth, TupleSecond), NumberGenericAppList, NumberGenericAppMaybe, NumberGenericAppTuple, PortEchoArrayStringTest, RecordNarrow01/02/03/04/05/06/08/09/10 and RecordOpenNarrowFieldIndexTest |
| `helper` | 9 | CompilerIssue2119MutualRecursionUnannotatedTest, CompilerIssue2207MutualRecursionSecondFunctionTest, CovForeignTypesTest, EntryMainOfRootModuleTest, ImportClosedTypeOpenItemTest, ImportExposingAllTest, ImportExposingItemsTest, ImportTypeByNameLaterReplacesTest, StandardA82MainInImportedModuleTest |
| `outside` | 3 | DictMapStagedCaptureTest (`Dict`), FunctionValuesChosenByIfCaseAndTupleTest (`Bitwise`, `Bytes.Encode`, `Bytes.Decode`), StandardA92BytesPortTest (`Bytes.Encode`, `Bytes.Decode`) |
| `parse-fail` | 3 | the three `Container*` tests |
| total | 628 | |

Library values used (scan): `Tuple.second` 13, `List.foldl` 11, `List.length` 9,
`Maybe.withDefault` 7, `Tuple.first` 6, `List.map` 6, `Maybe.map` 3, `Array.initialize`,
`Array.empty`, `Array.fromList`, `List.sum` 2 each, and `Array.append`, `List.range`,
`Array.push`, `String.length`, `Maybe.andThen`, `Array.toList`, `Array.map`, `List.foldr`,
`List.map2`, `Result.map`, `List.head` once each. This list is what step 9's static test basis
must bind at least (plan D2(b)).

#### 3.3 The summary printed by `--classify-static`

```
static classification: 939 elm-spec tests
  compile-error 311: parse-fail 18, lexical-accepted 8, syntactic 31, further 9,
    fixity-inference 1, static-deterministic 28, inference 216
  compile-success 628: B0 40, harness 540, library 33, helper 9, outside 3, parse-fail 3
```

The two compile-error numbers marked provisional in 2.4 (28 and 216) are final once the hand
review is done; their sum is 244 in any case.

### 4. The Appendix C extractor

#### 4.1 What it reads

From `definition/tex/appendix-static-basis.tex`:

| Source | Shape | Gives |
|--------|-------|-------|
| `fig:static-basis-tynames` (`tabular`) | rows `$t$ & k & bound to\\`, `t` a macro | the 22 type names of `T0`, arities, the type constructors bound to them |
| `\section{The Module Environment}`, the display after "has the domain" | `\{\kw{Basics}, \kw{List}, ...\}` with `\phantom{\{}` continuations | `Dom ME0` (19 modules) |
| the display defining `E_0`, `\TE_0`, `\VE_0` | prose display, VE-row syntax | `E0` |
| `fig:static-basis-basics-te` | TE rows | `TE` of `Basics` |
| `fig:static-basis-basics-ve1`, `-ve2` | VE rows, multi-name rows, continuation rows | `VE` of `Basics` |
| `fig:static-basis-operators` | four-column rows `ops & names & \mapsto & (σ, is)` | `OT_stat`, which identifiers the operators stand for, the module that declares each (`^{*}` marks `List`), precedence rank (row order) |
| `fig:static-basis-data`, `-platform`, `-task`, `-effects` | `\multicolumn{3}{|l|}{\kw{M}}` headings, TE rows above an `\hline`, VE rows below | the other interfaces |
| the paragraph "Hidden identifiers" and the TE of `Never` | prose, and constructors in a type structure absent from the module's VE | hidden identifiers: `JustOneMore` (Basics, type `Never`), `Perform` (Task, type `MyCmd`), `command` (Task) |
| the sentence "the set of operators that \kw{List} declares is $\{\kw{::}\}$" | prose | `smops(List) = {::}`, `smops(Basics) = Dom OT_stat \ {::}`, every other module `∅` |
| "the interfaces of \kw{List} and \kw{Tuple} are $(\emptymap, \emptymap, \emptymap)$" | prose | the two empty interfaces |
| `B_0 = T_0, \ME_0, \PE_0` with `\PE_0 = \emptymap` | prose | `PE0 = ∅` |

From `definition/tex/syntax-modules.tex`: `fig:default-imports`, eleven rows
`\kw{import ...}\\`.

The extractor locates each figure by its `\label{...}`, takes the text between the enclosing
`\begin{array}` (or `\begin{tabular}`) and its `\end`, and fails (a `FatalError` naming the
figure and the row) on anything it does not recognise. It never guesses: every row of every
listed figure must parse.

#### 4.2 Row shapes, all of which must be handled

1. **Simple VE row**: `\kw{toFloat}\citelabel{b:Basics.toFloat} & \mapsto & (\tInt \rightarrow \tFloat, \isv)`.
2. **Multi-name VE row**: `\kw{round}\citelabel{b:Basics.round},\ \kw{floor}\citelabel{b:Basics.floor} & \mapsto & (...)`:
   the first cell is a comma-separated list of `\kw{name}` each followed by zero or more
   `\citelabel{...}`/`\citealso{...}`; every name gets the same scheme and status.
3. **Continuation row**: a row whose first and second cells are empty (`& & ...`), possibly
   starting with `\phantom{...}`, `\quad` or `{}`: its third cell is appended to the third cell
   of the previous non-continuation row before parsing (rows 299-301 of the appendix: `clamp`;
   the `worker` record spans five rows).
4. **TE row with constructors**: `\kw{Bool}\citelabel{b:Basics.Bool} & \mapsto & (\tBool,\ \{\kw{True} \mapsto (\tBool, \isc),\ \kw{False} \mapsto (\tBool, \isc)\})`,
   with continuation rows (`Order`, `Maybe`, `Result`): the third cell is `(θ, VE)` whose second
   component is `\emptymap` or a brace list of VE entries.
5. **TE versus VE**: a row is a TE row exactly when the second component of its third cell is
   `\emptymap` or begins with `\{`; it is a VE row exactly when it ends in `\isc)` or `\isv)`. A
   row that is neither is an error. (The heading convention "TE rows come first and, below a
   rule, VE rows" is then checked, not relied on.)
6. **Module headings**: `\multicolumn{3}{|l|}{\kw{Maybe}}` starts the rows of `Maybe`;
   `\multicolumn{3}{|l|}{\kw{Json.Encode}\ \text{and}\ \kw{Json.Decode}}` starts rows that belong
   to both modules. In the three Basics figures there is no heading: the module is `Basics`, from
   the figure's label.
7. **Two labels on one name**: `\kw{Value}\citelabel{b:Json.Encode.Value}\citelabel{b:Json.Decode.Value}`.
8. **Operator rows** (four columns): `\kw{+},\ \kw{-} & \kw{add}\citelabel{b:Basics.add},\ \kw{sub}\citelabel{b:Basics.sub} & \mapsto & (...)`:
   the operators of the first cell are paired in order with the names of the second; the two
   lists must have equal length. `\kw{<{}<}` is `<<`, `\kw{\textasciicircum}` is `^`,
   `\kw{\&\&}` is `&&`, `\kw{::}^{*}` is `::` declared by `List`.
9. **Header rows** (`\var\ \text{or}\ \con & \mapsto & (\sigma, \is)`, `\tycon & \mapsto & ...`,
   `\opv & \text{stands for} & ...`) and `\hline` are skipped.
10. **Prose displays** (`E0`, `Dom ME0`, `T0`): parsed by the same scheme and VE-entry parsers,
    after removing `\phantom{...}`, `\quad`, `\\`, `&`, `\begin{array}...` wrappers.

#### 4.3 Type and scheme grammar

After removing `\,`, `\ `, `{}`, `\quad`, `\phantom{...}` (balanced braces) and line breaks,
the third cell is parsed by this grammar (the book's notation of Chapter 4, Figure
`fig:static-core-compound`):

```
pair     ::= "(" scheme "," status ")"              status ::= "\isc" | "\isv"
scheme   ::= "\forall" var+ "." type | type
var      ::= "\mv{" name "}"
type     ::= app ("\rightarrow" type)?             (right associative)
app      ::= atom tyname*                          (postfix: arguments before the name)
atom     ::= var | tyname | "(" type ")" | "(" type ("," type)+ ")" tyname
           | "\{" field ("," field)* "\}"          (a closed record; no open record occurs)
field    ::= "\kw{" label "}" "\mapsto" type
tyname   ::= "\tInt" | "\tFloat" | "\tChar" | "\tString" | "\tunit" | "\tList"
           | "\tTuple{2}" | "\tTuple{3}" | "\tBool" | "\sbtOrder" | "\sbtNever" | "\tMaybe"
           | "\sbtResult" | "\tArray" | "\tBytes" | "\tValue" | "\sbtCmd" | "\sbtSub"
           | "\sbtTask" | "\sbtProcessId" | "\sbtProgram" | "\sbtNode"
```

A sequence `(τ1, ..., τk) t` applies `t` to `k` arguments; `τ t` to one; `t` alone to none. The
arity of the result must equal `t`'s arity in `fig:static-basis-tynames`, else an error. The class
of a variable is from its spelling (A19, `static-core.tex`, `sec:static-core-simple`): the
extractor writes the spelling, and the reader computes the class.

#### 4.4 Validations (each failure is fatal)

- `tynames ME0 ⊆ T0` (`appendix-static-basis.tex`, `sec:appendix-static-basis-modenv`).
- `Dom ME0` from the display equals the set of modules with rows, plus `List` and `Tuple`.
- Every operator of Figure `fig:core-fixities` (`syntax-core.tex`) has a row in
  `fig:static-basis-operators`, and conversely (20 operators).
- Every default import names a module of `Dom ME0`; every item it exposes is in that module's
  interface, or is an operator of `smops` of the module (Appendix C, "Every module they name is
  in Dom ME0").
- In every TE row with constructors, each constructor of status `c` is either in the module's VE
  with the same scheme (an open type) or absent from it (a closed type, whose constructors are
  then hidden): only `Never` is closed.
- Every interface is well formed (`static-modules.tex`, `sec:static-modules-interfaces`).

### 5. JSON schemas

#### 5.1 `definition/mechanisation/static-basis.json`

```json
{
  "generatedBy": "definition/tools/src/ExtractStaticBasis.elm",
  "sources": [
    {"path": "definition/tex/appendix-static-basis.tex", "sha256": "..."},
    {"path": "definition/tex/syntax-modules.tex", "sha256": "..."}
  ],
  "typeNames": [
    {"key": "Int", "macro": "\\tInt", "arity": 0, "boundTo": ["Basics.Int"], "kind": "builtin"},
    {"key": "Tuple2", "macro": "\\tTuple{2}", "arity": 2, "boundTo": [], "kind": "builtin"},
    {"key": "Never", "macro": "\\sbtNever", "arity": 0, "boundTo": ["Basics.Never"], "kind": "custom-closed"},
    {"key": "Task", "macro": "\\sbtTask", "arity": 2, "boundTo": ["Platform.Task", "Task.Task"], "kind": "abstract"}
  ],
  "E0": {"TE": [TEENTRY], "VE": [VEENTRY]},
  "modules": [
    {"module": "Basics", "library": "elm/core", "TE": [TEENTRY], "VE": [VEENTRY], "ops": ["<<", ">>", "..."]},
    {"module": "List", "library": "elm/core", "TE": [], "VE": [], "ops": ["::"]}
  ],
  "operators": [
    {"op": "<<", "rank": 1, "standsFor": "composeL", "declaredBy": "Basics",
     "label": "b:Basics.composeL", "scheme": SCHEME, "status": "v"}
  ],
  "hidden": [
    {"module": "Basics", "name": "JustOneMore", "kind": "constructor", "typeName": "Never"},
    {"module": "Task", "name": "Perform", "kind": "constructor", "typeName": null, "note": "type MyCmd msg = Perform (Task Never msg); MyCmd is not in T0"},
    {"module": "Task", "name": "command", "kind": "value"}
  ],
  "PE0": [],
  "defaultImports": [
    {"module": "Basics", "as": null, "exposing": {"all": true}},
    {"module": "Debug", "as": null, "exposing": null},
    {"module": "List", "as": null, "exposing": {"items": [{"op": "::"}]}},
    {"module": "Maybe", "as": null, "exposing": {"items": [{"typeAll": "Maybe"}]}},
    {"module": "Platform.Cmd", "as": "Cmd", "exposing": {"items": [{"type": "Cmd"}]}}
  ]
}
```

where

```
TEENTRY ::= {"tycon": "Bool", "label": "b:Basics.Bool",
             "fcn": {"params": [], "body": TYPE}, "VE": [VEENTRY]}
VEENTRY ::= {"name": "True", "label": "b:Basics.Bool", "scheme": SCHEME, "status": "c" | "v"}
SCHEME  ::= {"forall": ["a", "b"], "body": TYPE}
TYPE    ::= {"var": "comparable"}                       (spelling; class by A19)
          | {"con": "List", "args": [TYPE]}             (con is a typeNames key)
          | {"fn": [TYPE, TYPE]}
          | {"record": [["init", TYPE], ...], "tail": null}
```

Order: `typeNames` as in the figure; `modules` in the order of `Dom ME0`'s display; entries of
a TE or VE in the order of the rows (a multi-name row gives its names in order); `operators` in
row order. Every type function of `T0`'s type names is the type name itself (`"params"` lists
`k` fresh spellings `"a1" ... "ak"` and the body applies the name to them), as the appendix
says ("the type functions they are bound to are the type names themselves"); an alias of the
basis (`Task.Task`, `Process.Id`, `Json.Decode.Value`, `Html.Html`) is recorded the same way.
The file is written with `Json.Encode.encode 2` and a final newline, so that `--check` compares
text.

#### 5.2 `definition/mechanisation/static-classification.json`

```json
{
  "generatedBy": "definition/tools/src/Translate.elm",
  "staticBasisSha256": "...",
  "counts": {
    "compileError": {"parse-fail": 18, "lexical-accepted": 8, "syntactic": 31, "further": 9,
                     "fixity-inference": 1, "static-deterministic": 28, "inference": 216},
    "compileSuccess": {"B0": 40, "harness": 540, "library": 33, "helper": 9, "outside": 3,
                       "parse-fail": 3}
  },
  "compileError": [
    {"project": "elm", "name": "ShadowingShadowingInLambdaTest",
     "modules": [{"path": "tests/elm/src/ShadowingShadowingInLambdaTest.elm", "parse": "ok"}],
     "parse": "ok",
     "rules": ["res:core-no-shadowing"],
     "rule": "res:core-no-shadowing",
     "class": "syntactic", "subclass": null, "step": 8,
     "trust": ["parse"],
     "title": "SHADOWING",
     "override": null}
  ],
  "compileSuccess": [
    {"project": "elm", "name": "HelloTest",
     "modules": [{"path": "tests/elm/src/HelloTest.elm", "parse": "ok"}],
     "parse": "ok",
     "basis": "harness",
     "needs": ["harness"],
     "main": "view", "mainAnnotated": false}
  ]
}
```

`step` is 8, 9 or 11 (`null` for the two `out` classes); `title` is the first `CHECK` line's
heading if it has the form `-- TITLE -`, else `null`; `override` is the override's `note` when
the table applied. Entries are sorted by project, then name.

### 6. The check of `Translate/Basis.elm`

`ExtractStaticBasis.elm` (both modes) compares the three functions of `Translate.Basis` with the
extraction:

- `value "" x` for every value `x` of `ME0(Basics)` (Basis.elm answers `value "Basics" x` by the
  same branch, so it is not counted twice), and `value m x` for every value of `ME0(Debug)` and
  `ME0(Char)`;
- `constructor k` for every constructor of `ME0(Basics)` and of the modules whose constructors
  the default imports expose (`Maybe`, `Result`);
- `operator o` for every operator of `OT_stat`.

For the converse list, `Translate.Basis` gains one export, `valueNames : List String`, the 30
names its `value` answers unqualified (a literal list beside the `case`, with a unit test that
`value "" x /= Nothing` for each), so that names Basis.elm binds and Appendix C does not can be
listed. Two schemes agree when there is a bijection between their quantified variables that preserves
the class (`Translate.Types.Class` against the class of the spelling) and makes the bodies equal
(`TCon` names are compared through the `typeNames` keys: `"Int"`, `"List"`, ...; `TTuple` of 2
or 3 against `Tuple2`, `Tuple3`; `TCon "()"`, if used, against `Unit`). It prints:

```
Basis.elm against Appendix C: 61 compared, 0 differ.
Absent from Basis.elm (9): Basics.logBase, Basics.degrees, Basics.radians, Basics.turns,
  Basics.toPolar, Basics.fromPolar, Basics.never, Result.Ok, Result.Err
In Basis.elm but bound by no interface of ME0 (1): append (OT_stat reaches it as ++; hidden)
```

The 61 are 29 values of `Basics` (all of Basis.elm's 30 unqualified values but `append`), 3 of
`Debug`, 2 of `Char`, 7 constructors (`True`, `False`, `LT`, `EQ`, `GT`, `Just`, `Nothing`) and
20 operators. A difference makes the script exit with a `FatalError` listing each. The "absent"
and "hidden" lists are informational: they change when step 2 encodes the rest of `Basics` and
`Ok`/`Err` (D3), and the step that changes them updates the expected output here.

### 7. Unit tests

`definition/tools/tests/StaticBasisTest.elm`, on literal strings copied from the appendix:

1. a simple VE row (`toFloat`) parses to one entry with the scheme `Int -> Float`;
2. the multi-name row `round, floor` gives two entries with one scheme;
3. the `max, min` row with its continuation line gives `∀comparable. comparable -> comparable -> comparable`;
4. the `Bool` TE row gives a type structure with `True` and `False`, status `c`;
5. the `Order` TE row with its `\phantom` continuation gives three constructors;
6. the `worker` row (five lines, a closed record of three fields) parses;
7. the operator row `+, -` gives two operators standing for `add` and `sub`; `\kw{::}^{*}` is
   declared by `List`;
8. the `Json.Encode` and `Json.Decode` heading assigns the `Value` row to both modules;
9. an arity mismatch (`\tList` with two arguments) is an error;
10. an unknown macro in a type is an error.

`definition/tools/tests/ClassifyTest.elm`, on small programs given as strings:

1. a test whose helper does not parse is `parse-fail`;
2. a test whose first resolved tag is `core-layout-rule` and which parses is `lexical-accepted`;
3. a test tagged `elm19-compile-error, elm-spec, modules-values-distinct` is `syntactic` with
   rule `res:modules-values-distinct` (the non-book tag is skipped);
4. a test tagged `s-exp-app` is `inference` unless overridden;
5. a compile-success program using `List.map` has `basis` `library` and `needs`
   `["library:List.map"]`; one with `import Html exposing (text)` and `main = text "x"` is
   `harness`, `main` `view`, not annotated;
6. `import Platform.Cmd as Cmd` then `Cmd.none` is not a library use.

## Tests gained

None: step 7 proves nothing. It fixes the sets that steps 8, 9 and 11 must prove: the 31
`syntactic` tests (step 8), the 9 `further` and the `static-deterministic` tests (step 9), the
`inference` and `fixity-inference` tests (step 11), and the positive targets of step 9 (the
compile-success tests whose `basis` is not `outside` or `parse-fail`: 622).

## Acceptance

Run from the repository root, in this order:

```
site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm
site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm --check
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --classify-static
(cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm)
```

Expected:

1. `ExtractStaticBasis.elm` writes `static-basis.json` and prints `static basis: 22 type names,
   19 modules, 20 operators, 3 hidden identifiers, 11 default imports`, then the Basis.elm lines
   of section 6 with `0 differ`. With `--check`: `static-basis.json is up to date.`
2. The translator prints its usual summary unchanged (`elm-spec tests: 939, translated: 491`,
   the refusal counts as before: the classification adds no refusal) and `written: N files` with
   N one more than before the step. `--check` prints `Lean translations are up to date.`
3. `--classify-static` prints the summary of section 3.3. The compile-error numbers 18, 8, 31, 9,
   1 and the sum 244 are exact; 28 and 216 are as the hand review settles them, stated in the
   report. The compile-success numbers may differ from the scan of 3.2 only with an explanation
   in the report, test by test, and must sum to 628.
4. The elm-test suite passes, with the 16 new tests of section 7 and the `valueNames` test of
   section 6.
5. `lake build` and `lake exe run-examples` are not affected (no Lean change); the general
   acceptance of the plan (site data, link audit, reports) applies: the mechanisation report gets
   a dated block "Step 7" with the two summaries; the plan's "Test inventory" Part II paragraph is
   replaced by the measured numbers.

## Risks and fallbacks

- **The extractor is brittle against edits of the appendix.** That is intended: it fails loudly,
  and the fix is to extend the row grammar. If the appendix's layout changes often, the fallback
  is P2-12's other option: move the figures to a generated table, as
  `DerivedForms/Table.elm` does for Appendix A, and generate both the LaTeX and the JSON from it.
  Not done now, because the appendix is stable and the book is the source.
- **The hand review is a judgement.** Each override carries a note, and the class is tested by
  the step that proves it: a test that step 9 cannot refuse without inference is moved to
  `inference` by step 9, with the reason.
- **The library scan undercounts names that reach a module through `exposing (..)`.** The
  classifier resolves imports properly; the scan's numbers are guidance only.
- **elm-syntax upgrades** change the parse column. The version is pinned by `elm.json`; an
  upgrade reruns the classification and the report lists the changes.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **The count of syntactic refusals.** The plan says "syntactic restrictions decidable on a
   syntax tree, 37". Measured: 31 parsed tests whose rule is AST-decidable; the 37 included one
   `res:core-annotation-placement` test and one `res:modules-header` test (both trusted to the
   parser, plan "Out of scope") and four tests elm-syntax does not parse
   (RecordUpdateNoFieldsTest, ImportAliasQualifiedTest, TopLevelPatternBindingTest,
   UnexpectedPatternFloatWithExponentTest). The plan's "about 19" lexical or grammar errors are
   18 that do not parse plus 8 that parse wrongly (`lexical-accepted`). Followed: the measured
   numbers; the plan's inventory paragraph should be replaced by them.
2. **"Parses it as Elm does"** (plan, step 7's line in "Order of work" and the trust table) cannot
   be checked with the tools available; this specification drops it as a check (2.6) and keeps
   it as the `[parse]` trust, with the 8 `lexical-accepted` tests as recorded counter-evidence.
3. **B0 count.** The plan's earlier "42 elaborate in B0" is 40 by the scan; the classifier fixes
   it.

## Progress

**2026-11-11: done.**

- `ExtractStaticBasis.elm`, `StaticBasis/Latex.elm`, `StaticBasis/Extract.elm`,
  `StaticBasis/Json.elm`: `static basis: 22 type names, 19 modules, 20 operators, 3 hidden
  identifiers, 11 default imports`; `Basis.elm against Appendix C: 70 compared, 0 differ`, nothing
  absent, nothing extra (step 2 encoded the rest of `Basics` and `Ok`/`Err`, so the specification's
  "61 compared" and its absent list are out of date). `--check` reports the file up to date.
- `Translate/Classify.elm`, `Translate/ClassifyOverrides.elm`, the translator's
  `static-classification.json` and option `--classify-static`:

  ```
  static classification: 939 elm-spec tests
    compile-error 311: parse-fail 18, lexical-accepted 8, syntactic 31, further 9,
      fixity-inference 1, static-deterministic 28, inference 216
    compile-success 628: B0 39, harness 540, library 34, helper 9, outside 3, parse-fail 3
  ```

  The compile-success numbers differ from the scan of 3.2 by one test: PortEchoJsonValueTest
  uses `Json.Encode.int` and seven other `Json.Encode` functions, which Appendix C does not bind,
  so it is `library`, not `B0`.
- `Translate.Basis.valueNames` (36 names). 126 unit tests (`StaticBasisTest`, `ClassifyTest` and
  the earlier ones).

Differences from this specification:
- The override table is the specification's provisional review (section 2.4), checked against the
  tests' tags and `-- COMPILE-ERROR:` texts, and, for the one `r:s-ty-openrecord` test, by reading
  it (CompilerIssue2200ConstrainedExtensibleErrorCrashTest: an open record whose row variable is
  `number`). The 216 `inference` tests were not each read by hand; step 9 moves any test it cannot
  refuse without inference, or step 11 finds one it can, and says so.
- The JSON writes each module's `parse` as `"ok"`/`"fail"`, and `title` from the first CHECK line
  of the form `-- TITLE -`.

