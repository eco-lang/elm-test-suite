# Runtime tests (rt.txt) against the book

Counts: OK 139, WRONG 1, TAG 1, UNSURE 7 (total 148)

Convention used: Debug.log prints `label: Debug.toString v` each time the book's evaluation applies it (README); Floats print as String.fromFloat (App. E, Debug), so an integral Float prints without ".0". CHECK lines are unordered (README). Effects tests assume the echo host and an execution that makes progress (the book does not require progress, A86).

| Test | Verdict | Notes |
|---|---|---|
| tests/elm/src/ArrayAppendCanonicalTest.elm | OK | Array equality by the lists (fig:dynamic-basis-eq clause 4); Array.append/initialize as elm/core. |
| tests/elm/src/ArrayEqAfterPushTest.elm | OK | As above. |
| tests/elm/src/CaseFanOutShadowTest.elm | OK | r1 = 3 + 4//2 = 5; -1; 0. |
| tests/elm/src/CaseResultTest.elm | OK | 42, -1, 100. |
| tests/elm/src/CharCasePredicateTest.elm | OK | "comma". |
| tests/elm/src/CompilerIssue2019AliasOfTypeVariableTest.elm | OK | testFailure1 1: number unfixed, Float by A27 revised; prints "1" (Floats print as String.fromFloat, App. E Debug). |
| tests/elm/src/CompilerIssue2119MutualRecursionUnannotatedTest.elm | OK | depth (Succ Zero) = 1; imported unannotated group elaborates. |
| tests/elm/src/CompilerIssue2182ExtensibleFunctionAliasCrashTest.elm | WRONG | Book rejects the program. In `type alias Goal a = { a \| field : Int } -> a`, `a` is a row variable (sm-typbind notation; s-ty-openrecord, s-ty-rowvar), so `Goal { field : Int }` substitutes the closed record {field:Int} for a row that already has `field`; the substitution is undefined (static-core, substitution: "a row variable can never give a record type a second field with a label it already has", A23), so s-ty-con does not apply and `solution`/`puzzle` annotations do not elaborate. Suggest: make it a COMPILE-ERROR test (or elm-spec-contradicts, XFAIL), noting the book rejects both alike. |
| tests/elm/src/CompilerIssue2207MutualRecursionSecondFunctionTest.elm | OK | g 3 at Float (A27 default): counts down to 0, prints "0". |
| tests/elm/src/CompilerIssue2281LongLineListTest.elm | OK | 22000 elements counted (checked by script). |
| tests/elm/src/CoreIssue1141UnusedPortCallBreaksSubscriptionTest.elm | OK | Subscription current from the Start update (p-update); echoed value accepted (p-in-accept). Relies on the echo host. |
| tests/elm/src/CovEtaDebugLogTest.elm | OK | 3 + 4 = 7. |
| tests/elm/src/CovForeignTypesTest.elm | OK | 41 + 1 = 42. |
| tests/elm/src/CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest.elm | OK | ((5+1)*2)-3 = 9. |
| tests/elm/src/CovPortIncomingArrayTest.elm | OK | Port declaration elaborates (Array is a payload type); testValue = 1 at Float prints "1". |
| tests/elm/src/CovPortIncomingJSONValueTest.elm | OK | As above. |
| tests/elm/src/CovPortIncomingTripleTest.elm | OK | As above. |
| tests/elm/src/CovPortIncomingUnitTest.elm | OK | As above. |
| tests/elm/src/CovPortOutgoingJSONValueTest.elm | OK | As above. |
| tests/elm/src/CovPortOutgoingUnitTest.elm | OK | As above. |
| tests/elm/src/CustomTypeMultiFieldTest.elm | OK | CHECK matches only the label; could be `person: Person "Alice" 30 True`. |
| tests/elm/src/CustomTypeNestedTest.elm | OK | CHECK matches only the label; could be `nested: Node (Leaf 1) (Node (Leaf 2) (Leaf 3))`. |
| tests/elm/src/DebugLogLambdaBoundaryTest.elm | OK | "hi" twice. |
| tests/elm/src/DebugLogRecordTupleFieldTest.elm | OK | CHECKs are unordered, so field/component order (App. E) does not matter. |
| tests/elm/src/DebugNumberAtFloatTest.elm | OK | Outputs right. Note: under A27 revised `showAll 2` uses the default (Float) copy, not Int; the comment ("the Int values") and label showAllInt are stale; same text "2","4" either way. |
| tests/elm/src/DictMapStagedCaptureTest.elm | OK | 10+5, 20+5. |
| tests/elm/src/EntryMainOfRootModuleTest.elm | OK | Root main logs "root" (p-dyn-main); helper main is also evaluated (p-dyn-module) and logs "helper", which no CHECK forbids. |
| tests/elm/src/EtaExpandSeventeenArgumentAliasTest.elm | OK | unused = useBig ... = 0 never calls wide; testValue = 1 (Float) prints "1". |
| tests/elm/src/FlagsRecordTest.elm | OK | "native-flags", 43, True. |
| tests/elm/src/FunctionValuesChosenByIfCaseAndTupleTest.elm | OK | 5 - 5 + 18 + 14 + 2 + 4 = 38. |
| tests/elm/src/HelloTest.elm | OK |  |
| tests/elm/src/ImportClosedTypeOpenItemTest.elm | OK | sm-item-opentype comment: T(..) of a closed type imports the type and no constructors. |
| tests/elm/src/ImportExposingAllTest.elm | OK | [42,101,7,3]. |
| tests/elm/src/ImportExposingItemsTest.elm | OK | 42, [0,7], 3, 5, 101. |
| tests/elm/src/ImportTypeByNameLaterReplacesTest.elm | OK | sm-item-type comment: a type listed by name replaces an earlier one. |
| tests/elm/src/LetNumberAndThenTest.elm | OK | 30 at Float, round 45. |
| tests/elm/src/LetNumberArrayMapTest.elm | OK | [45,60]. |
| tests/elm/src/LetNumberAsPatternTest.elm | OK | 45 + 70 = 115 (both components at Float). |
| tests/elm/src/LetNumberBoxedSilentMiscompileTest.elm | OK | 45, 45, [45,60], 45, [45]. |
| tests/elm/src/LetNumberContainerDualTest.elm | OK | Outputs right. Note: under A27 revised `intUse = Tuple.first t + 1` is itself number-polymorphic and its only use (Debug.log) fixes nothing, so it is the Float default copy (31.0 prints "31"); the Int use the comment describes no longer happens. Annotate `intUse : Int` to keep the dual use. |
| tests/elm/src/LetNumberDualUseTest.elm | OK | Genuine dual use (toFloat forces Int): 9, 15, 3, 5, 3, 5, 5; round 2.5 = 3 (fig:dynamic-basis-conv). |
| tests/elm/src/LetNumberFoldrTest.elm | OK | 105. |
| tests/elm/src/LetNumberIndirectFoldlTest.elm | OK | acc0 at Float, 4.0 rounds to 4. |
| tests/elm/src/LetNumberListOfClosuresTest.elm | OK | [30,31]. |
| tests/elm/src/LetNumberListOfMaybeTest.elm | OK | [45,60]. |
| tests/elm/src/LetNumberListOfRecordsTest.elm | OK | [45,60]. |
| tests/elm/src/LetNumberLogBaseTest.elm | OK | logBase by its text (appendix-dynamic-basis, elementary functions); round gives 2. |
| tests/elm/src/LetNumberMap2Test.elm | OK | [45,60]. |
| tests/elm/src/LetNumberMaybeChainTest.elm | OK | 45/3 = 15. |
| tests/elm/src/LetNumberResultMapTest.elm | OK | 45. |
| tests/elm/src/LetNumberSumMapTest.elm | OK | 105. |
| tests/elm/src/LetNumberTupleBothTest.elm | OK | 45 + 60 = 105. |
| tests/elm/src/LetNumberTupleSecondTest.elm | OK | 45. |
| tests/elm/src/LetSeparatedStagingTest.elm | TAG | The file has no CHECK line, so no output is compared and none of d-exp-case, d-exp-lambda, d-atexp-let, s-valbind-var is actually checked (only that the program runs). Book value: caseFunc 0 10 5 3 = 18. Suggest adding `-- CHECK: result: 18`. |
| tests/elm/src/LetValueBindingTest.elm | OK | 21, 42 (x is the Float default copy; prints the same). |
| tests/elm/src/ListLiteralDebugLogKindTest.elm | OK | d has Int and Float copies (both used); all CHECK-DAG values right; repeated "d:" lines harmless. |
| tests/elm/src/NoImportsTest.elm | OK | 1 + 2 at Float prints "3". |
| tests/elm/src/NonEntryMainEvaluatedOnceTest.elm | UNSURE | The book evaluates NonEntryMainAux.main once (p-dyn-module comment, A59), but A59 and App. E (sec:appendix-implementation-order, Top-level Values) let an implementation evaluate a top-level value later or repeatedly, and record eco printing a Debug.log in a top-level value once per use as conforming; Debug.log output is outside the definition (A62). So the CHECK-NOT (two auxMain lines) and the CHECK-NEXT adjacency test an implementation choice. Suggest tag elm-unspecced, or drop the CHECK-NOT and turn CHECK-NEXT into CHECK. |
| tests/elm/src/NumberGenericAppList.elm | OK | 45. |
| tests/elm/src/NumberGenericAppMaybe.elm | OK | 45. |
| tests/elm/src/NumberGenericAppTuple.elm | OK | 45. |
| tests/elm/src/OutgoingPortTuple3KeepsRunningTest.elm | OK | "sent" in init, "after" after the sleep. |
| tests/elm/src/OutgoingPortTuple3Test.elm | OK |  |
| tests/elm/src/PlatformManagerCommandTest.elm | UNSURE | Random.generate is a command of a manager of the platform (p-disp-plat); which managers exist and what they give is a platform parameter (A83, p-platform comment; App. E Managers and Programs: eco natively discards Random commands). The book does not determine that "generated: 7" is logged. Suggest elm-unspecced (or keep only as a platform test). |
| tests/elm/src/PortAliasEchoTest.elm | OK | Alias port type expands (s-ty-con); record round-trips. |
| tests/elm/src/PortEchoArrayStringTest.elm | OK |  |
| tests/elm/src/PortEchoBoolTest.elm | OK |  |
| tests/elm/src/PortEchoFloatTest.elm | OK | 0 in a List Float is the Float 0, prints "0"; -1e-7 per String.fromFloat (App. E). |
| tests/elm/src/PortEchoIntTest.elm | UNSURE | 9007199254740991 and -9007199254740991 lie outside the Int range the body guarantees (-2^31..2^31-1, sec:appendix-implementation-int, A40); their value as Int constants and at the port depends on the implementation parameter IntRange. README puts "an integer constant outside the Int range" under elm-unspecced. Suggest dropping those two values (and CHECKs) or tagging elm-unspecced; the other five are fine. |
| tests/elm/src/PortEchoJsonValueTest.elm | OK | Json.Encode.encode is library code; key order as the host preserves it. |
| tests/elm/src/PortEchoListIntTest.elm | OK |  |
| tests/elm/src/PortEchoMaybeIntTest.elm | OK |  |
| tests/elm/src/PortEchoNestedTest.elm | OK |  |
| tests/elm/src/PortEchoStringTest.elm | OK | NUL printed as \0 per Elm/JS Debug.toString. |
| tests/elm/src/PortEchoTest.elm | OK |  |
| tests/elm/src/PortEchoTuple2Test.elm | OK |  |
| tests/elm/src/PortEchoTuple3Test.elm | OK |  |
| tests/elm/src/PortEchoUnitTest.elm | OK |  |
| tests/elm/src/PortEncodingDecodeFloatTest.elm | OK | Port declaration elaborates; ambiguous names from exposing (..) unused (sm-explist-all); testValue 0 prints "0". |
| tests/elm/src/PortEncodingDecodeListIntTest.elm | OK | As above. |
| tests/elm/src/PortEncodingDecodeMaybeIntTest.elm | OK | As above. |
| tests/elm/src/PortEncodingDecodeTuple2Test.elm | OK | As above. |
| tests/elm/src/PortEncodingEncodeBoolTest.elm | OK | As above. |
| tests/elm/src/PortEncodingEncodeFloatTest.elm | OK | As above. |
| tests/elm/src/PortEncodingEncodeMaybeRecordTest.elm | OK | As above. |
| tests/elm/src/PortEncodingEncodeTuple2Test.elm | OK | As above. |
| tests/elm/src/PortEncodingPortWithArrayTest.elm | OK | As above. |
| tests/elm/src/PortIncomingRejectTest.elm | OK | null at String rejected (p-in-reject, A71); "ok" accepted. |
| tests/elm/src/PureMutualRecursiveValueTest.elm | OK | Delayed mutual references allowed; ok: (). |
| tests/elm/src/PureRecursiveValueThunkTest.elm | OK |  |
| tests/elm/src/RecordNarrow01CapturesNonEmptyTest.elm | OK | 999 + 999 = 1998. |
| tests/elm/src/RecordNarrow02CapturesNothingTest.elm | OK | 1998. |
| tests/elm/src/RecordNarrow03FullAnnotationTest.elm | OK | 1998. |
| tests/elm/src/RecordNarrow04SingleFieldTest.elm | OK | 1998. |
| tests/elm/src/RecordNarrow05NoNestingTest.elm | OK | 1998. |
| tests/elm/src/RecordNarrow06RowPolyAnnotationTest.elm | OK | 1998. |
| tests/elm/src/RecordNarrow08NoDestructureTest.elm | OK | LambdaId 999. |
| tests/elm/src/RecordNarrow09DirectCallTest.elm | OK | 999. |
| tests/elm/src/RecordNarrow10TripleNestingTest.elm | OK | 1998. |
| tests/elm/src/RecordOpenNarrowFieldIndexTest.elm | OK | 1998. |
| tests/elm/src/RecordRowsTest.elm | OK | 3, "p", (1,2) (constructor follows written field order y, x), 5. |
| tests/elm/src/ResultErrTest.elm | OK | Err 404 at Float prints "Err 404". |
| tests/elm/src/ResultOkTest.elm | OK |  |
| tests/elm/src/StandardA56PrefixAndOrTest.elm | OK | (&&)/(\|\|) are basic values applied to two values (appendix-dynamic-basis, A56), so both Debug.log arguments are evaluated; results False, True. (Strictness is visible only through Debug.log output, the suite convention.) |
| tests/elm/src/StandardA72AbsentFlagsTest.elm | OK | Absent flags are null, Maybe Int decodes Nothing (A72). |
| tests/elm/src/StandardA82MainInImportedModuleTest.elm | OK | Helper main : Int = 42 is an ordinary value (A82); 43. |
| tests/elm/src/StandardA87NumberDefaultCopyTest.elm | UNSURE | Values right: Int copy of x is 0, so x // 1 is 0; the default Float copy is 0.5 and is evaluated in the book (sec:dynamic-core-numbers). But the first CHECK observes the evaluation of an unused copy only through Debug.log, whose output is outside the definition (A62), and App. E (sec:appendix-implementation-numbers) records eco, which makes only the copies a program uses and so never logs, as conforming on copies; the test comment says so too. Suggest tag elm-unspecced for the first CHECK (or the test). |
| tests/elm/src/StandardA88PortNegativeZeroTest.elm | OK | -0 crosses as the number 0, received as +0 at Float (A88); 1/+0 > 0. |
| tests/elm/src/StandardA88PortNonFiniteTest.elm | OK | NaN and infinity go out as null (A88), decode to Nothing twice. |
| tests/elm/src/StandardA92BytesPortTest.elm | OK | Bytes is a payload type (A92); [1,2,255]. |
| tests/elm/src/StandardA97NeverErrBranchTest.elm | OK | Err branch irredundant (A97, coinductive inhabitants); 3. |
| tests/elm/src/StandardA97SelfOnlyTypeTest.elm | OK | Accepted (A97); 3. |
| tests/elm/src/StringEscapesTest.elm | OK | newline/tab CHECKs match only labels; quote right. |
| tests/elm/src/TypeAliasCtorTest.elm | OK | { bold = True, count = 42 }. |
| tests/elm/src/WideClosureArity300Test.elm | OK | 1882518 recomputed by script from the 300 arguments and terms. |
| tests/elm/src/WideRecord1100Test.elm | OK | Field values checked by script; pattern (1000,False), update True, eq True/False. |
| tests/elm/src/WideRecord600Test.elm | OK | As above. |
| tests/elm/src/WideRecordDecoder26Test.elm | OK | base 1: 1000, 1024, 1025. |
| tests/elm/src/WideRecordDecoder300Test.elm | OK | Checked fields recomputed by script. |
| tests/elm/src/WideRecordDecoder30Test.elm | OK | 1000, 1024, 25.5, 'a', 1027, "28s", 1029. |
| tests/elm/src/WideRecordDecoder70Test.elm | OK | All 12 checked fields recomputed. |
| tests/elm/src/WideRecordGcBitmapTest.elm | OK | 50000 + 150000 = 200000; "pa". |
| tests/elm-core/src/CmdBatchOrderTest.elm | UNSURE | Expects reverse order ([3,2,1], [5,4,3,2,1]). The order in which the commands of a batch are dispatched is unspecified (A66; p-disp-out comment: with Cmd.batch [send 1, send 2] either value may be delivered first; programs.tex conformance: "the order of the commands of a batch ... is left open"); the reverse order is only what both implementations do (App. E, The Order of Commands). Suggest elm-unspecced, or check the sorted lists. |
| tests/elm-core/src/CmdMapComposeTest.elm | OK | "x then g then f" (e-msg-map). |
| tests/elm-core/src/ContainerCompareIntTest.elm | OK | fig:dynamic-basis-order, lexicographic. Note: unannotated literals are Float under A27 revised (only emptyInts is Int); results identical. |
| tests/elm-core/src/ContainerEqualityFloatTest.elm | OK | +0 = -0, NaN unequal (fig:dynamic-basis-eq clause 2). |
| tests/elm-core/src/ContainerEqualityIntTest.elm | OK | Note: literals are Float under A27 revised, so tripleMinMax compares Floats, not the Int extremes; still True. |
| tests/elm-core/src/CoreIssue1110PortDeclarationOrderTest.elm | OK | As 1141. |
| tests/elm-core/src/CoreIssue1123NestedCmdBatchStackOverflowTest.elm | OK | Flattening (effects.tex) gives one task leaf; no resource bound in the body. |
| tests/elm-core/src/CoreIssue1150CharToCodeLoneSurrogateTest.elm | UNSURE | Book: Char.fromCode 0xD800 gives other(n), a character whose code is some Int in IntRange distinct from every other code (appendix-dynamic-basis, A52); the code may be negative. The regex `code: [0-9]+` rejects a negative code. Suggest `{{code: -?[0-9]+(\n\|$)}}`. |
| tests/elm-core/src/CoreIssue1154PortSubscribedWithCmdTest.elm | OK | "init" echo may give no message (no current subscription, A66 note); "hello" arrives after the Start update. |
| tests/elm-core/src/CoreIssue955KillProcessTwiceTest.elm | OK | Killing an ended process changes nothing (p-proc-kill, A80). |
| tests/elm-core/src/CoreIssue960PowNegativeExponentIntTest.elm | OK | Int 2 ^ -1 is 0 (A43); regex accepts it (could be tightened to `pow: 0`). |
| tests/elm-core/src/FloatNaNTest.elm | OK | nanProp CHECK matches only the label. |
| tests/elm-core/src/ProcessKillRunnableTest.elm | UNSURE | Both "survived queued" (required) and the absence of "survived runnable" depend on how the parent and child processes interleave after Process.spawn. The book lets any steps come between two steps of a process, which may be suspended at any andThen (p-proc-step comment, A78; programs.tex: "the interleaving of processes is left open"), so the child may be killed before it logs, or the runnable child may log before the kill. Suggest elm-unspecced. |
| tests/elm-core/src/ProcessPrimitiveOutcomeTest.elm | OK | sleep and kill succeed with (). |
| tests/elm-core/src/ProcessSpawnKillHalfTest.elm | OK | Odd processes are never killed, so they fire; no CHECK-NOT for even ones, so the timing of the kills is not tested. |
| tests/elm-core/src/ProcessSpawnRecursiveTest.elm | OK |  |
| tests/elm-core/src/ProcessSpawnedFailureEndsTest.elm | OK | Failing spawned process ends silently (p-proc-end). |
| tests/elm-core/src/ProcessYieldThrashingTest.elm | OK | CHECKs unordered. |
| tests/elm-core/src/StandardA81SleepBeyond32BitsTest.elm | OK | sleep 3e9 acts no sooner than 3e9 ms (p-proc-sleep, A81); killed at ~200 ms. |
| tests/elm-core/src/TaskAttemptErrorTest.elm | OK |  |
| tests/elm-core/src/TaskOnErrorCascadeTest.elm | OK | 10 + 20 + 30 = 60. |
| tests/elm-core/src/TaskOnErrorInnerTest.elm | OK | 70, 5. |
| tests/elm-core/src/TaskOnErrorSucceedTest.elm | OK | Handler not applied (e-task-onerror-succeed). |
| tests/elm-core/src/TaskPerformValueTest.elm | OK | `Task.succeed -7` is an application to a negation (syntax-core negation). |
| tests/elm-core/src/TaskSucceedAsArgTest.elm | OK |  |
| tests/elm-core/src/TimerEffectTest.elm | OK |  |
