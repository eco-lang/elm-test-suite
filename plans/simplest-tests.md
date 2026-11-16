# The simplest test of every rule and restriction

**Status (2026-11-15): done.** 62 new `elm-spec` tests in `tests/elm/src/Minimal*Test.elm`, with
four helper modules (`MinimalHelper*.elm`). All pass on Elm 0.19.1, 0.19.2, 0.19.3 and Lamdera
1.5.0, and all are translated into Lean and proved end to end (`scripts/verify.sh full`).

## Why

Many `elm-spec` tests came from eco's compiler test suite, where they were written to force rare
compilation paths. A rule tagged only by such a test is checked, but a failure of the test does not
point at the rule. The simplest test of a rule exercises it with as few other rules as the language
allows, so that its failure points to that rule.

## The criterion

For every rule and restriction (`runner/spec-items.js`: 194 rules, 39 restrictions), the `elm-spec`
tests of the `elm` project that tag it were measured: the number of tokens of the program, leaving
out comments, the module header, imports and the standard `main` that logs `testValue`; and the
number of book items the test tags. An item already had a simplest test when one of its tests has
at most 25 tokens (90 for the rules of effects and programs, whose programs need a worker) and
tags at most four items. 121 items did not. Four rules had no `elm-spec` test at all:
`dm-topdec-port-in`, `dm-topdec-port-out`, `p-disp-plat` and `p-platform`.

For each of them the smallest program that needs the rule was written:

- **Expressions, matches and patterns:** `testValue` is one expression of the construct, such as
  `{ a = 1 }`, `(7)` or `case 2 of 1 -> 10 ; _ -> 20`. A static rule and its dynamic twin share
  a test, since every program that runs is first elaborated. A rule that fails a pattern has its own
  test beside the rule that matches it.
- **Type expressions:** one annotation of the form (`same : a -> a`, `testValue : (Int)`).
- **Modules:** one helper module per kind of exposing item (by name, `(..)`, a record alias, a type
  with its constructors).
- **Tasks and processes:** a worker whose `init` gives one command and whose `update` logs the
  message, with the smallest task that needs the rule.
- **Encoding and decoding at a port:** a pipe at one type (`plans/host-pipe-tests.md`), one value
  each; true and false, `Nothing` and `Just` are separate tests.

Tests tag only their subjects, as the README asks.

## Items with no new test

- **`d-match-fail`:** none possible. A match fails as a whole only when every rule fails, which an
  exhaustive match (`res:core-exhaustiveness`) never does; a lambda's match is one irrefutable rule.
  CaseOrderTest and CaseBranchSelectionTest tag it; see `plans/test-review-candidates.md`.
- **`p-disp-plat`, `p-platform`:** none within `elm-spec`. Which managers a platform has is a
  parameter of the platform (ruling A83); PlatformManagerCommandTest (`elm-unspecced`) records what
  Elm/JS does.
- **Near minimal already:** NoImportsTest (`dm-imports-empty`, `sm-imports-empty`: a module
  without imports must build its `main` from `Platform.worker` itself), RecordUpdateNoFieldsTest
  (`core-record-update-form`), TopLevelPatternBindingTest (`modules-no-top-pattern`),
  StandardA84DuplicatePortNameTest (`modules-program`: two ports of one name need two modules),
  StandardA88PortNonFiniteTest (`e-enc-float-null`: a non-finite Float can only be made by the
  program, so it is sent out and read back through the echo host), PortPipeBytesTest
  (`e-enc-bytes`, `e-dec-bytes`).

## Every item

"new" names the Minimal test(s) that are now its simplest; "existing" the smallest test that met
the criterion before (its size in tokens).

| Item | Kind | Simplest test |
|------|------|---------------|
| `d-atexp-scon` | rule | existing: StringEscapesTest (21 tokens) |
| `d-atexp-var` | rule | new: MinimalVariableTest |
| `d-atexp-con` | rule | existing: MaybeNothingTest (11 tokens) |
| `d-atexp-op` | rule | existing: CombinatorWConcatTest (22 tokens) |
| `d-atexp-unit` | rule | new: MinimalUnitTest |
| `d-atexp-tuple` | rule | existing: TupleCharFieldTest (19 tokens) |
| `d-atexp-nil` | rule | new: MinimalEmptyListTest |
| `d-atexp-record` | rule | new: MinimalRecordTest |
| `d-atexp-update` | rule | new: MinimalRecordUpdateTest |
| `d-atexp-paren` | rule | new: MinimalParenthesesTest |
| `d-atexp-let` | rule | new: MinimalLetTest |
| `d-exprow-field` | rule | new: MinimalRecordTest |
| `d-exp-atexp` | rule | new: MinimalConstantTest |
| `d-exp-app` | rule | existing: StandardApplicationStrictTest (24 tokens) |
| `d-exp-lambda` | rule | existing: FunctionChainedPartialApplicationTest (18 tokens) |
| `d-exp-case` | rule | new: MinimalCaseTest |
| `d-app-closure` | rule | existing: FunctionChainedPartialApplicationTest (18 tokens) |
| `d-app-con` | rule | existing: ResultErrTest (22 tokens) |
| `d-app-basic-partial` | rule | existing: CombinatorWConcatTest (22 tokens) |
| `d-app-basic-apply` | rule | existing: CombinatorWConcatTest (22 tokens) |
| `d-match-first` | rule | new: MinimalCaseTest |
| `d-match-fail` | rule | none possible: a match fails as a whole only when every rule fails, which an exhaustive match (res:core-exhaustiveness) never does |
| `d-match-next` | rule | new: MinimalCaseNextRuleTest |
| `d-mrule-match` | rule | new: MinimalCaseTest |
| `d-mrule-fail` | rule | new: MinimalCaseNextRuleTest |
| `d-dec-nonrec` | rule | new: MinimalLetTest |
| `d-dec-rec` | rule | new: MinimalLetRecursionTest |
| `d-valbind-var` | rule | new: MinimalLetTest |
| `d-valbind-pat` | rule | new: MinimalDestructuringTest |
| `d-atpat-wild` | rule | new: MinimalCaseNextRuleTest |
| `d-atpat-scon` | rule | new: MinimalConstantPatternTest |
| `d-atpat-scon-fail` | rule | new: MinimalCaseNextRuleTest |
| `d-atpat-var` | rule | new: MinimalCaseTest |
| `d-atpat-con` | rule | new: MinimalConstructorPatternTest |
| `d-atpat-con-fail` | rule | new: MinimalConstructorPatternFailTest |
| `d-atpat-unit` | rule | new: MinimalUnitPatternTest |
| `d-atpat-tuple` | rule | new: MinimalTuplePatternTest |
| `d-atpat-nil` | rule | new: MinimalNilPatternTest |
| `d-atpat-nil-fail` | rule | new: MinimalNilPatternFailTest |
| `d-atpat-record` | rule | new: MinimalRecordPatternTest |
| `d-atpat-paren` | rule | new: MinimalParenthesisedPatternTest |
| `d-patrow-field` | rule | new: MinimalRecordPatternTest |
| `d-pat-atpat` | rule | new: MinimalCaseTest |
| `d-pat-con` | rule | new: MinimalConstructedPatternTest |
| `d-pat-con-fail` | rule | new: MinimalConstructedPatternFailTest |
| `d-pat-cons` | rule | new: MinimalConsPatternTest |
| `d-pat-cons-fail` | rule | new: MinimalConsPatternFailTest |
| `d-pat-as` | rule | new: MinimalAsPatternTest |
| `dm-module` | rule | new: MinimalImportValueTest |
| `dm-header` | rule | new: MinimalImportValueTest |
| `dm-imports-import` | rule | existing: CovForeignTypesTest (15 tokens) |
| `dm-imports-empty` | rule | existing, near minimal: NoImportsTest |
| `dm-explist-all` | rule | new: MinimalExposingAllTest |
| `dm-explist-items` | rule | new: MinimalImportValueTest |
| `dm-expitem-var` | rule | new: MinimalImportValueTest |
| `dm-expitem-op` | rule | existing: ImportOperatorItemTest (24 tokens) |
| `dm-expitem-alias` | rule | new: MinimalExposingAliasTest |
| `dm-expitem-type` | rule | existing: ImportClosedTypeConstructorTest (16 tokens) |
| `dm-expitem-open` | rule | new: MinimalExposingOpenTest |
| `dm-topdec-val` | rule | existing: CompilerIssue2207MutualRecursionSecondFunctionTest (14 tokens) |
| `dm-topdec-type` | rule | new: MinimalCustomTypeTest |
| `dm-topdec-alias` | rule | new: MinimalTypeAliasTest |
| `dm-topdec-port-out` | rule | new: MinimalPipeIntTest |
| `dm-topdec-port-in` | rule | new: MinimalPipeIntTest |
| `dm-topdec-seq` | rule | new: MinimalVariableTest |
| `dm-datbind` | rule | new: MinimalCustomTypeTest |
| `dm-conbind` | rule | new: MinimalCustomTypeTest |
| `dm-typbind` | rule | new: MinimalTypeAliasTest |
| `e-task-andthen-succeed` | rule | new: MinimalTaskAndThenTest |
| `e-task-andthen-fail` | rule | new: MinimalTaskAndThenFailTest |
| `e-task-onerror-fail` | rule | new: MinimalTaskOnErrorTest |
| `e-task-onerror-succeed` | rule | new: MinimalTaskOnErrorSucceedTest |
| `e-task-andthen-inner` | rule | new: MinimalTaskAndThenInnerTest |
| `e-task-onerror-inner` | rule | new: MinimalTaskOnErrorInnerTest |
| `e-task-prim` | rule | new: MinimalSleepTest |
| `e-enc-int` | rule | new: MinimalPipeIntTest |
| `e-enc-float` | rule | new: MinimalPipeFloatTest |
| `e-enc-float-null` | rule | existing, near minimal: StandardA88PortNonFiniteTest |
| `e-enc-true` | rule | new: MinimalPipeTrueTest |
| `e-enc-false` | rule | new: MinimalPipeFalseTest |
| `e-enc-string` | rule | new: MinimalPipeStringTest |
| `e-enc-bytes` | rule | existing, near minimal: PortPipeBytesTest |
| `e-enc-unit` | rule | new: MinimalPipeUnitTest |
| `e-enc-nothing` | rule | new: MinimalPipeNothingTest |
| `e-enc-just` | rule | new: MinimalPipeJustTest |
| `e-enc-list` | rule | new: MinimalPipeListTest |
| `e-enc-array` | rule | new: MinimalPipeArrayTest |
| `e-enc-tuple` | rule | new: MinimalPipeTupleTest |
| `e-enc-record` | rule | new: MinimalPipeRecordTest |
| `e-enc-value` | rule | new: MinimalPipeValueTest |
| `e-dec-int` | rule | new: MinimalPipeIntTest |
| `e-dec-float` | rule | new: MinimalPipeFloatTest |
| `e-dec-true` | rule | new: MinimalPipeTrueTest |
| `e-dec-false` | rule | new: MinimalPipeFalseTest |
| `e-dec-string` | rule | new: MinimalPipeStringTest |
| `e-dec-bytes` | rule | existing, near minimal: PortPipeBytesTest |
| `e-dec-unit` | rule | new: MinimalPipeUnitTest |
| `e-dec-nothing` | rule | new: MinimalPipeNothingTest |
| `e-dec-just` | rule | new: MinimalPipeJustTest |
| `e-dec-list` | rule | new: MinimalPipeListTest |
| `e-dec-array` | rule | new: MinimalPipeArrayTest |
| `e-dec-tuple` | rule | new: MinimalPipeTupleTest |
| `e-dec-record` | rule | new: MinimalPipeRecordTest |
| `e-dec-value` | rule | new: MinimalPipeValueTest |
| `e-msg-task` | rule | new: MinimalTaskPerformTest |
| `e-msg-port` | rule | new: MinimalPortSubscriptionTest |
| `e-msg-map` | rule | new: MinimalCmdMapTest |
| `p-stat-module` | rule | new: MinimalImportValueTest |
| `p-stat-main-program` | rule | existing: BadMainTypeTypeVariableMainTest (3 tokens) |
| `p-stat-main-view` | rule | existing: BadMainTypeTypeVariableMainTest (3 tokens) |
| `p-dyn-module` | rule | existing: StandardA82MainInImportedModuleTest (15 tokens) |
| `p-dyn-main` | rule | existing: HelloTest (14 tokens) |
| `p-program` | rule | existing: ImportedModuleTypeErrorTest (16 tokens) |
| `p-disp-empty` | rule | existing: NoImportsTest (50 tokens) |
| `p-disp-task` | rule | new: MinimalTaskPerformTest |
| `p-disp-out` | rule | new: MinimalPipeIntTest |
| `p-disp-plat` | rule | none possible within `elm-spec`: which managers a platform has is a parameter of the platform (A83); PlatformManagerCommandTest (`elm-unspecced`) records Elm/JS |
| `p-init` | rule | existing: StandardA72AbsentFlagsTest (60 tokens) |
| `p-update` | rule | new: MinimalTaskPerformTest |
| `p-proc-step` | rule | new: MinimalTaskAndThenTest |
| `p-proc-sleep` | rule | new: MinimalSleepTest |
| `p-proc-spawn` | rule | new: MinimalSpawnTest |
| `p-proc-kill` | rule | new: MinimalKillTest |
| `p-proc-message` | rule | new: MinimalTaskPerformTest |
| `p-proc-end` | rule | new: MinimalSpawnTest |
| `p-in-accept` | rule | existing: PortIncomingRejectTest (83 tokens) |
| `p-in-reject` | rule | existing: PortIncomingRejectTest (83 tokens) |
| `p-out` | rule | new: MinimalPipeIntTest |
| `p-wait` | rule | new: MinimalSleepTest |
| `p-platform` | rule | the same as p-disp-plat |
| `program-modules-distinct` | restriction | existing: File (11 tokens) |
| `program-import-order` | restriction | existing: ImportCycleTest (11 tokens) |
| `program-modules-reachable` | restriction | existing: UnreachableModuleTest (11 tokens) |
| `program-main` | restriction | existing: BadMainRecursiveUnannotatedMainTest (10 tokens) |
| `s-atexp-scon` | rule | existing: TooManyArgsTooManyArgumentsToALiteralTest (4 tokens) |
| `s-atexp-longvar` | rule | new: MinimalVariableTest |
| `s-atexp-longcon` | rule | existing: TooManyArgsTooManyArgumentsToAConstructorTest (5 tokens) |
| `s-atexp-op` | rule | existing: TypeMismatchArgumentToAnOperatorFunctionTest (5 tokens) |
| `s-atexp-unit` | rule | new: MinimalUnitTest |
| `s-atexp-tuple` | rule | existing: BadTupleATupleOfFourTest (11 tokens) |
| `s-atexp-nil` | rule | new: MinimalEmptyListTest |
| `s-atexp-record` | rule | new: MinimalRecordTest |
| `s-atexp-update` | rule | new: MinimalRecordUpdateTest |
| `s-atexp-let` | rule | new: MinimalLetTest |
| `s-atexp-paren` | rule | new: MinimalParenthesesTest |
| `s-exprow` | rule | new: MinimalRecordTest |
| `s-exp-atexp` | rule | new: MinimalConstantTest |
| `s-exp-app` | rule | existing: TooManyArgsTooManyArgumentsToALiteralTest (4 tokens) |
| `s-exp-lambda` | rule | existing: TypeMismatchAccessorUnderIntTest (7 tokens) |
| `s-exp-case` | rule | new: MinimalCaseTest |
| `s-match` | rule | new: MinimalCaseTest |
| `s-mrule` | rule | new: MinimalCaseTest |
| `s-dec-group` | rule | existing: LetNumberLogBaseTest (22 tokens) |
| `s-valbind-var` | rule | existing: TypeMismatchCharUnderIntTest (6 tokens) |
| `s-valbind-pat` | rule | new: MinimalDestructuringTest |
| `s-ty-tyvar` | rule | new: MinimalTypeVariableTest |
| `s-ty-rowvar` | rule | new: MinimalRowVariableTest |
| `s-ty-record` | rule | new: MinimalRecordTypeTest |
| `s-ty-openrecord` | rule | new: MinimalRowVariableTest |
| `s-ty-unit` | rule | new: MinimalUnitTest |
| `s-ty-tuple` | rule | existing: TypeMismatchTupleSizesDifferTest (16 tokens) |
| `s-ty-con` | rule | existing: QualifiedTypeNotExposedTest (10 tokens) |
| `s-ty-fun` | rule | new: MinimalTypeVariableTest |
| `s-ty-paren` | rule | new: MinimalParenthesisedTypeTest |
| `s-tyrow` | rule | new: MinimalRecordTypeTest |
| `s-atpat-wild` | rule | new: MinimalCaseNextRuleTest |
| `s-atpat-scon` | rule | new: MinimalConstantPatternTest |
| `s-atpat-var` | rule | new: MinimalCaseTest |
| `s-atpat-con` | rule | new: MinimalConstructorPatternTest |
| `s-atpat-unit` | rule | new: MinimalUnitPatternTest |
| `s-atpat-tuple` | rule | new: MinimalTuplePatternTest |
| `s-atpat-nil` | rule | new: MinimalNilPatternTest |
| `s-atpat-record` | rule | new: MinimalRecordPatternTest |
| `s-atpat-paren` | rule | new: MinimalParenthesisedPatternTest |
| `s-patrow` | rule | new: MinimalRecordPatternTest |
| `s-pat-atpat` | rule | new: MinimalCaseTest |
| `s-pat-con` | rule | new: MinimalConstructedPatternTest |
| `s-pat-cons` | rule | new: MinimalConsPatternTest |
| `s-pat-as` | rule | new: MinimalAsPatternTest |
| `core-irredundancy` | restriction | existing: RedundantPatternABranchAfterAWildcardTest (16 tokens) |
| `core-exhaustiveness` | restriction | existing: MissingPatternsAMissingListLengthTest (20 tokens) |
| `sm-module` | rule | existing: File (11 tokens) |
| `sm-header` | rule | existing: ImportUnexposedValueTest (11 tokens) |
| `sm-imports-import` | rule | existing: ImportResolutionQualifiedImportedFunctionTest (12 tokens) |
| `sm-imports-empty` | rule | existing, near minimal: NoImportsTest |
| `sm-explist-all` | rule | existing: ImportResolutionQualifiedImportedFunctionTest (12 tokens) |
| `sm-explist-items` | rule | new: MinimalImportValueTest |
| `sm-item-var` | rule | existing: CompilerIssue2207MutualRecursionSecondFunctionTest (14 tokens) |
| `sm-item-op` | rule | existing: ImportUnknownOperatorTest (4 tokens) |
| `sm-item-type` | rule | existing: ImportClosedTypeConstructorTest (16 tokens) |
| `sm-item-opentype` | rule | existing: ImportAliasOpenItemTest (4 tokens) |
| `sm-topdec-value` | rule | existing: RecordAccessorFunctionCaseTest (12 tokens) |
| `sm-topdec-types` | rule | new: MinimalTypeAliasTest |
| `sm-topdec-portout` | rule | existing: PortProblemCharPayloadTest (7 tokens) |
| `sm-topdec-portin` | rule | existing: PortEncodingDecodeFloatTest (14 tokens) |
| `sm-topdec-seq` | rule | existing: TypeMismatchAliasNamedLikeAnImportedTypeTest (18 tokens) |
| `sm-datbind` | rule | existing: TypeMismatchLocalTypeNamedLikeAnImportedOneTest (21 tokens) |
| `sm-conbind` | rule | existing: TooManyArgsTooManyArgumentsToANullaryConstructorTest (8 tokens) |
| `sm-typbind` | rule | existing: TypeMismatchTypeWhereAnAliasTest (11 tokens) |
| `sm-typbind-record` | rule | new: MinimalRecordAliasConstructorTest |
| `core-escape-unicode` | restriction | existing: ParseErrorStringEscapeTooFewDigitsTest (3 tokens) |
| `core-identifier-characters` | restriction | existing: NonAsciiIdentifierTest (20 tokens) |
| `core-constant-separated` | restriction | existing: ParseErrorNumberBadHexDigitTest (4 tokens) |
| `core-adjacent-items` | restriction | existing: StandardA1UnitPatternGapTest (23 tokens) |
| `core-layout-rule` | restriction | existing: WeirdElseBranchElseNotIndentedTest (13 tokens) |
| `core-operator-chain` | restriction | existing: InfixNonAssocCompareTest (12 tokens) |
| `core-row-labels-distinct` | restriction | existing: NameClashARecordFieldGivenTwiceTest (11 tokens) |
| `core-pattern-row-label-only` | restriction | existing: StandardA99RecordPatternRowPunRejectedTest (16 tokens) |
| `core-record-update-form` | restriction | existing, near minimal: RecordUpdateNoFieldsTest |
| `core-field-selection` | restriction | existing: CovForeignTypesTest (15 tokens) |
| `core-binding-site-distinct` | restriction | existing: NameClashTwoArgumentsOfOneNameTest (10 tokens) |
| `core-no-shadowing` | restriction | existing: ShadowingShadowingInLambdaTest (7 tokens) |
| `core-no-float-pattern` | restriction | existing: UnexpectedPatternFloatWithExponentTest (16 tokens) |
| `core-annotation-placement` | restriction | existing: AnnotationNotFollowedByDefinitionTest (19 tokens) |
| `core-let-recursion` | restriction | existing: CyclicValueALetValueDefinedByItselfTest (10 tokens) |
| `modules-ports` | restriction | existing: CovPortOutgoingJSONValueTest (19 tokens) |
| `modules-header` | restriction | existing: ModuleHeaderMissingImportedTest (11 tokens) |
| `modules-import-alias` | restriction | existing: ImportAliasQualifiedTest (4 tokens) |
| `modules-basics-qualifier` | restriction | existing: StandardA91BasicsAliasTest (13 tokens) |
| `modules-no-operator-exposing` | restriction | existing: HeaderExposesOperatorTest (15 tokens) |
| `modules-header-exposing` | restriction | existing: HeaderExposesUndeclaredValueTest (4 tokens) |
| `modules-exposing-distinct` | restriction | existing: HeaderExposesTwiceTest (4 tokens) |
| `modules-no-top-pattern` | restriction | existing, near minimal: TopLevelPatternBindingTest |
| `modules-values-distinct` | restriction | existing: TopLevelValueTwiceTest (17 tokens) |
| `modules-types-distinct` | restriction | existing: TopLevelTypeAndAliasSameNameTest (14 tokens) |
| `modules-constructors-distinct` | restriction | existing: TopLevelConstructorTwiceTest (14 tokens) |
| `modules-no-shadowing` | restriction | existing: ShadowingAnArgumentShadowingATopLevelValueTest (13 tokens) |
| `modules-tyvarseq-distinct` | restriction | existing: TypeParameterTwiceTest (12 tokens) |
| `modules-custom-type-tyvars` | restriction | existing: CustomTypeUnboundVariableTest (9 tokens) |
| `modules-alias-tyvars` | restriction | existing: AliasUnboundVariableTest (10 tokens) |
| `modules-alias-not-recursive` | restriction | existing: AliasProblemQualifiedTypeTest (9 tokens) |
| `modules-value-recursion` | restriction | existing: CyclicDefinitionATopLevelValueDefinedByItselfTest (8 tokens) |
| `modules-program` | restriction | existing, near minimal: StandardA84DuplicatePortNameTest |
