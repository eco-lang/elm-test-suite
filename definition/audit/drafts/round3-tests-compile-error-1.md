# Compile-error tests (ce1): check against A Standard Definition of Elm?

154 tests, all in tests/elm/src, all tagged elm-spec and expected to be refused.
Every tag in these tests was checked to name an existing book label (rule, restriction, figure).

Counts: OK 153, TAG 1, WRONG 0, UNSURE 0.

General note: many tests here are modules with `exposing (..)` and no `main`. As programs (Chapter 9)
they are also refused by program-main; the verdicts below judge the module-level reason the test
is about, which refuses them independently.

| Test | Verdict | Refusing rule / restriction | Note |
|---|---|---|---|
| AliasProblemExtensibleRecordUnitTupleAndFunctionTest | OK | modules-alias-not-recursive | A occurs unqualified in its own type |
| AliasProblemQualifiedTypeTest | OK | modules-alias-not-recursive | A occurs unqualified inside Maybe.Maybe (List A) |
| AliasProblemRecursiveAliasWithCommentedParensTest | OK | modules-alias-not-recursive | |
| AliasUnboundVariableTest | OK | modules-alias-tyvars | |
| AliasUnusedParameterTest | OK | modules-alias-tyvars | "exactly the type variables": no unused parameter |
| AnnotationNotFollowedByDefinitionTest | OK | core-annotation-placement | |
| BadMainRecursiveMainTest | OK | program-main; p-stat-main-program / p-stat-main-view | main and f form one group, so main is not bound alone; Int -> Int is neither Program nor Node |
| BadMainRecursiveUnannotatedMainTest | OK | program-main; p-stat-main-program / p-stat-main-view | as above; principal type is a function type |
| BadMainTypeAliasMainTest | OK | p-stat-main-program / p-stat-main-view | |
| BadMainTypeFunctionMainTest | OK | p-stat-main-program / p-stat-main-view | |
| BadMainTypeRecordMainTest | OK | p-stat-main-program / p-stat-main-view | |
| BadMainTypeThreeArgumentTypeMainTest | OK | p-stat-main-program / p-stat-main-view | |
| BadMainTypeTypeVariableMainTest | OK | p-stat-main-program / p-stat-main-view | principal scheme forall a. List a (A96); Dflt gives List a |
| BadMainTypeUnitMainTest | OK | p-stat-main-program / p-stat-main-view | |
| BadTupleATupleOfFourTest | TAG | grammar, fig:core-grammar-expressions (A12) | A four-tuple is not a phrase: the grammar admits 2 or 3 components (syntax-core.tex l.511; rule comment of s-atexp-tuple "By the grammar k is 2 or 3"). s-atexp-tuple never applies to it. Add fig:core-grammar-expressions (keeping s-atexp-tuple is harmless) |
| CaseCharEscapedDuplicateTest | OK | core-irredundancy | constants cover the same character however written (A31) |
| CharLiteralSurrogateEscapeTest | OK | core-escape-unicode | surrogate range excluded (A8) |
| CompilerIssue1491PhantomTupleUnsoundTest | OK | s-exp-app | needs m = OnePlus m |
| CompilerIssue1550RecordExtensionDuplicateFieldTest | OK | s-ty-con | A B: substitution undefined (duplicate x, A23) |
| CompilerIssue1639LetAnnotationTypeVarCrashTest | OK | s-valbind-var | explicit a would have to be free in C (U' disjoint from tyvars C) |
| CompilerIssue1669InfiniteTypeArrayGetSetHangTest | OK | s-exp-app | needs a = Arr (Arr a) |
| CompilerIssue1691ContradictoryExtensibleRecordHangTest | OK | s-exp-app | combineAB: {fieldA, a'} = {fieldB, a'} impossible |
| CompilerIssue1700InfiniteTypeFoldrLambdaHangTest | OK | s-exp-app (via s-atexp-op for ::) | infinite type |
| CompilerIssue1748DestructureMissingFieldCrashTest | OK | s-atpat-record (field iDontExist absent from { window : Int }); s-exp-app | Note: `foo : Float` is also applied to arguments in `foo iDontExist <| bar model`, an independent s-exp-app error; the test would be refused even with the field. Consider tagging s-exp-app or making foo a function |
| CompilerIssue1785ExtensibleAliasOfUnitTest | OK | s-ty-con | row parameter applied to () |
| CompilerIssue1789RankCrashMissingJustTest | OK | s-valbind-var / s-match | formData = Maybe formData with formData explicit |
| CompilerIssue1839RigidLetAnnotationCrashTest | OK | s-valbind-var | escape of explicit a |
| CompilerIssue1866PhantomExtensibleRecordHangTest | OK | s-exp-app; s-valbind-var | {a1 / r} vs {a2 / r}; also `bug configure = ()` against Html msg |
| CompilerIssue1896ExtendCustomTypeCrashTest | OK | s-ty-con | |
| CompilerIssue1951OpenRecordLetCrashTest | OK | s-exp-app | closed { future : {} } lacks tool |
| CompilerIssue1952ExtendIntCrashTest | OK | s-ty-con | |
| CompilerIssue1974RankCrashWrongAnnotationTest | OK | s-valbind-var / s-exp-app | head : a == toRemove : String with a explicit |
| CompilerIssue1975LetOrderCrashTest | OK | s-exp-app | a is both a record and a Type |
| CompilerIssue2001RankCrashParametricLetAnnotationTest | OK | s-valbind-var | escape of explicit a |
| CompilerIssue2006IndexOutOfBoundsMaybeWithDefaultTest | OK | s-exp-app | model would be { cog : Int } but needs entry |
| CompilerIssue2013RankCrashLambdaLetAnnotationTest | OK | s-valbind-var | |
| CompilerIssue2014RankCrashIdentityLetAnnotationTest | OK | s-valbind-var | t : a, annotation claims h |
| CompilerIssue2027IncompatibleExtensibleRecordsHangTest | OK | s-exp-app | |
| CompilerIssue2036LensRecordUpdateHangTest | OK | s-exp-app | explicit inputState would have to be a record |
| CompilerIssue2064ExtendStringNotEnoughBytesTest | OK | s-ty-con | |
| CompilerIssue2066RankCrashNumberFloatTest | OK | s-valbind-var | explicit number vs Float (also s + c : number vs Float) |
| CompilerIssue2072ExtendUnitInResultCrashTest | OK | s-ty-con | Tagged () |
| CompilerIssue2077RankCrashExtensibleLetAnnotationTest | OK | s-valbind-var | |
| CompilerIssue2083ExtendCustomTypeFieldAccessCrashTest | OK | s-ty-con | Article (extensible alias) declares no constructor, so no clash with Preview's Article |
| CompilerIssue2097ExtensibleUnitArgCrashTest | OK | s-ty-con | |
| CompilerIssue2100LetAnnotationRank2CrashTest | OK | s-valbind-var | body () against { value : String } |
| CompilerIssue2105ExtensibleFoldlCrashTest | OK | s-exp-app | |
| CompilerIssue2106FoldlExtensibleRecordHangTest | OK | s-exp-app | |
| CompilerIssue2108IfBranchExtensibleRecordHangTest | OK | s-match (df:if) | branch types cannot agree |
| CompilerIssue2112CaseBranchInfiniteTypeHangTest | OK | s-match | a = Maybe a |
| CompilerIssue2146RoseLambdaPatternCrashTest | OK | s-valbind-var | explicit a would be Rose c |
| CompilerIssue2148RecordUpdateFoldrCrashTest | OK | s-atpat-record (df:field-selection), s-atexp-update | Model = {} |
| CompilerIssue2153RecursiveCallWrongArgCrashTest | OK | s-exp-app / s-valbind-var | |
| CompilerIssue2176ExtensibleUnitAliasCrashTest | OK | s-ty-con | |
| CompilerIssue2184LetRecursionTooManyArgsCrashTest | OK | s-exp-app | Int applied to an argument |
| CompilerIssue2200ConstrainedExtensibleErrorCrashTest | OK | s-ty-openrecord | only a variable of class any names a row variable (A36) |
| CompilerIssue2206RecordUpdateLetCrashTest | OK | s-atexp-update | two : () vs Custom |
| CompilerIssue2214LensSetterArgumentOrderHangTest | OK | s-exp-app | |
| CompilerIssue2241FoldMapInfiniteTypeHangTest | OK | s-exp-app | |
| CompilerIssue2274MutualRecursionTransmuteTest | OK | s-valbind-var | f : forall a b. a -> b -> b (group monomorphic, A24), so eraseType : a -> b is too general |
| CompilerIssue2295LambdaLetAnnotationCrashTest | OK | s-valbind-var | |
| CompilerIssue2296LetAnnotationFreeVarCrashTest | OK | s-valbind-var | |
| CompilerIssue2301InnerSkolemOuterVarCrashTest | OK | s-valbind-var | |
| CompilerIssue2338LambdaLetAnnotationTupleCrashTest | OK | s-valbind-var | |
| CustomTypeUnboundRowVariableTest | OK | modules-custom-type-tyvars | |
| CustomTypeUnboundVariableTest | OK | modules-custom-type-tyvars | |
| CyclicDefinitionATopLevelValueDefinedByItselfTest | OK | modules-value-recursion | |
| CyclicValueALetValueDefinedByItselfTest | OK | core-let-recursion | |
| HeaderExposesAliasOpenTest | OK | modules-header-exposing | |
| HeaderExposesConstructorByNameTest | OK | modules-header-exposing | |
| HeaderExposesOperatorTest | OK | modules-no-operator-exposing | |
| HeaderExposesTwiceTest | OK | modules-exposing-distinct | |
| HeaderExposesTypeTwiceTest | OK | modules-exposing-distinct | |
| HeaderExposesUndeclaredValueTest | OK | modules-header-exposing | |
| ImportAliasOpenItemTest | OK | sm-item-opentype | Point is a record alias in ModuleExposingHelper (constructor of status v) |
| ImportAliasQualifiedTest | OK | modules-import-alias | |
| ImportClosedTypeConstructorTest | OK | sm-item-type (no constructor imported), so s-atexp-longcon has no binding for Shape | Borderline: the failing premise is in s-atexp-longcon; adding it would be more exact |
| ImportCycleTest | OK | program-import-order | helpers ImportCycleA/B import each other |
| ImportUnexposedValueTest | OK | sm-header (interface lacks hidden), so s-atexp-longvar fails | Borderline: the failing premise is in s-atexp-longvar; adding it would be more exact |
| ImportUnknownOperatorTest | OK | sm-item-op | |
| ImportedModuleTypeErrorTest | OK | p-program (helper fails by s-exp-app: 1 + "one") | p-stat-module / s-atexp-op would be more exact but p-program does fail |
| InfiniteTypeSelfAppliedArgumentOnBothSidesTest | OK | s-exp-app | also (x, number) vs (x, String) in the list |
| InfixAssocRightConsAppendTest | OK | s-exp-app (fig:core-fixities grouping) | |
| InfixMixedAssocComposeTest | OK | core-operator-chain | |
| InfixMixedAssocPipesTest | OK | core-operator-chain | |
| InfixNoQualifiedOperatorTest | OK | fig:core-grammar-expressions | |
| InfixNoSectionLeftTest | OK | fig:core-grammar-expressions | |
| InfixNoSectionRightTest | OK | fig:core-grammar-expressions | |
| InfixNonAssocCompareTest | OK | core-operator-chain | |
| InfixNonAssocEqTwiceTest | OK | core-operator-chain | |
| LetCycleThroughRecordLambdaTest | OK | core-let-recursion | |
| MissingPatternsAMissingListLengthTest | OK | core-exhaustiveness | |
| MissingPatternsAMissingTupleShapeTest | OK | core-exhaustiveness | |
| ModuleHeaderMissingImportedTest | OK | modules-header | |
| NameClashARecordFieldGivenTwiceTest | OK | core-row-labels-distinct | |
| NameClashTwoArgumentsOfOneNameTest | OK | core-binding-site-distinct | |
| NameClashTwoLetBindingsOfOneNameTest | OK | core-binding-site-distinct | the definitions of one let are one binding site |
| NamingErrorAnUnknownVariableTest | OK | s-atexp-longvar | |
| ParseErrorCasePatternUnfinishedTest | OK | fig:core-grammar-patterns | |
| ParseErrorNumberBadHexDigitTest | OK | core-constant-separated | 0x1 followed by inner character g |
| ParseErrorNumberFractionThenLetterTest | OK | core-constant-separated | |
| ParseErrorStringEscapeTooFewDigitsTest | OK | core-escape-unicode | four to six digits |
| ParseErrorStringEscapeUnclosedTest | OK | core-escape-unicode | no other sequence beginning with backslash is an escape |
| PortProblemCharPayloadTest | OK | sm-topdec-portout | Port(Char) fails (fig:static-modules-port) |
| PortProblemDeclarationWithoutNameTest | OK | fig:grammar-top-level-declarations | |
| QualifiedTypeNotExposedTest | OK | s-ty-con | `foo = foo` also breaks modules-value-recursion (second, independent reason) |
| RecordUpdateNoFieldsTest | OK | core-record-update-form | |
| RedundantPatternABranchAfterAWildcardTest | OK | core-irredundancy | 0 elaborates at Int (s-atpat-scon) |
| ShadowingAnArgumentShadowingATopLevelValueTest | OK | modules-no-shadowing | |
| ShadowingShadowingInLambdaTest | OK | core-no-shadowing | |
| StandardA1UnitPatternGapTest | OK | core-adjacent-items | A1 |
| StandardA84DuplicatePortNameTest | OK | modules-program (port names distinct, A84); the side condition fails in p-stat-main-program | The clash is found when the main module (last) is elaborated, by p-stat-main-program; the helper passes p-stat-module. Tag p-stat-main-program in place of (or beside) p-stat-module |
| StandardA8SurrogateEscapeTest | OK | core-escape-unicode | A8 |
| StandardA91BasicsAliasTest | OK | modules-basics-qualifier | A91 |
| StandardA97MaybeNeverMissingJustTest | OK | core-exhaustiveness | A97: Just (JustOneMore ...) uncovered |
| TooFewArgsAConstructorPatternWithTooFewArgumentsTest | OK | s-pat-con | |
| TooManyArgsAConstructorPatternWithTooManyArgumentsTest | OK | s-pat-con | |
| TooManyArgsTooManyArgumentsToAConstructorTest | OK | s-exp-app | |
| TooManyArgsTooManyArgumentsToAFunctionTest | OK | s-exp-app | |
| TooManyArgsTooManyArgumentsToALambdaTest | OK | s-exp-app | |
| TooManyArgsTooManyArgumentsToALiteralTest | OK | s-exp-app / s-atexp-scon | no function type is in Adm(number) |
| TooManyArgsTooManyArgumentsToALocalTest | OK | s-exp-app / s-atexp-longvar | |
| TooManyArgsTooManyArgumentsToANullaryConstructorTest | OK | s-exp-app | |
| TooManyArgsTooManyArgumentsToAnOperatorTest | OK | s-exp-app / s-atexp-op | |
| TopLevelConstructorTwiceTest | OK | modules-constructors-distinct | |
| TopLevelPatternBindingTest | OK | modules-no-top-pattern | |
| TopLevelPortAndValueSameNameTest | OK | modules-values-distinct | |
| TopLevelRecordAliasConstructorClashTest | OK | modules-constructors-distinct | record alias P declares constructor P |
| TopLevelTypeAndAliasSameNameTest | OK | modules-types-distinct | |
| TopLevelValueTwiceTest | OK | modules-values-distinct | |
| TypeConstructorTooFewArgsTest | OK | s-ty-con | arity |
| TypeExprUnitAppliedTest | OK | fig:core-grammar-types | |
| TypeMismatchAccessOnANumberTest | OK | s-atpat-record via df:field-selection, s-exp-app | |
| TypeMismatchAccessOnAnEmptyRecordTest | OK | s-atpat-record via df:field-selection, s-exp-app | |
| TypeMismatchAccessorUnderIntTest | OK | s-valbind-var (df:field-accessor is a lambda) | |
| TypeMismatchAliasNamedLikeAnImportedTypeTest | OK | s-exp-app | local Bool (C plus E, sm-topdec-seq) is Int, Basics.True is Bool |
| TypeMismatchAliasWhereARecordTest | OK | s-valbind-var | |
| TypeMismatchAliasedRecordFieldOfTheWrongTypeTest | OK | s-valbind-var | |
| TypeMismatchAppendableAgainstATupleTest | OK | s-exp-app | |
| TypeMismatchArgumentOfAFixedConstructorPatternTest | OK | s-pat-con | "a" : String, T takes Int |
| TypeMismatchArgumentToAConstructorTest | OK | s-exp-app | |
| TypeMismatchArgumentToAnOperatorFunctionTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolLeftOfAppendTest | OK | s-exp-app / s-atexp-op | Bool not appendable |
| TypeMismatchBoolLeftOfMinusTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolLeftOfPowerTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolLeftOfTimesTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolPatternTest | OK | s-exp-case | Bool not in Adm(number) |
| TypeMismatchBoolRightOfAppendWithAStringTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolRightOfPlusTest | OK | s-exp-app / s-atexp-op | |
| TypeMismatchBoolsComparedTest | OK | s-exp-app / s-atexp-op | Bool not comparable |
| TypeMismatchCaseAsAnArgumentTest | OK | s-exp-app | |
| TypeMismatchCharUnderIntTest | OK | s-valbind-var | |
| TypeMismatchClosedRecordWhereExtensibleTest | OK | s-valbind-var / s-exp-app | |
| TypeMismatchCompappendAgainstARigidVarTest | OK | s-valbind-var / s-atexp-op | explicit a (class any) not admissible for appendable |
