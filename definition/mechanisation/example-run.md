# Standard Elm mechanisation: example run

Programs: 579 (38 workers), in 16 shards; checks: 1708.

## Elm01

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| AccessorFunctionFieldInListTest | results | [11,20] | [11,20] | agree | t_elm_AccessorFunctionFieldInListTest |
| AccessorFunctionFieldTailCallTest | results | [2,11,142,42] | [2,11,142,42] | agree | t_elm_AccessorFunctionFieldTailCallTest |
| AccessorPlaceholderAccessorOfAFunctionFieldPassedInTailCallsTest | testValue | 8 | 8 | agree | t_elm_AccessorPlaceholderAccessorOfAFunctionFieldPassedInTailCallsTest |
| AccessorToLocalFuncTest | result | 42 | 42 | agree | t_elm_AccessorToLocalFuncTest |
| AccessorVariableTest | via_var | 42 | 42 | agree | t_elm_AccessorVariableTest |
| AccessorVariableTest | mapped | [10,20,30] | [10,20,30] | agree | t_elm_AccessorVariableTest |
| AccessorVariableTest | person_name | "Alice" | "Alice" | agree | t_elm_AccessorVariableTest |
| AccessorVariableTest | company_name | "ACME" | "ACME" | agree | t_elm_AccessorVariableTest |
| AliasForwardTest | dupInt | 3 | 3 | agree | t_elm_AliasForwardTest (native) |
| AliasForwardTest | dupStr | "a!!" | "a!!" | agree | t_elm_AliasForwardTest (native) |
| AliasForwardTest | foldInt | 6 | 6 | agree | t_elm_AliasForwardTest (native) |
| AliasForwardTest | foldFloat | 45 | 45 | agree | t_elm_AliasForwardTest (native) |
| AliasForwardTest | mapPartial | 5 | 5 | agree | t_elm_AliasForwardTest (native) |
| AliasForwardTest | value | 4 | 4 | agree | t_elm_AliasForwardTest (native) |
| AnnotatedLetRecFnResultTest | AnnotatedLetRecFnResultTest | 16 | 16 | agree | t_elm_AnnotatedLetRecFnResultTest |
| AnonymousFunctionTest | lambda1 | [2,4,6] | [2,4,6] | agree | t_elm_AnonymousFunctionTest |
| AnonymousFunctionTest | lambda2 | 15 | 15 | agree | t_elm_AnonymousFunctionTest |
| AnonymousFunctionTest | lambda3 | [2,4] | [2,4] | agree | t_elm_AnonymousFunctionTest |
| AppendTypeSplitTest | strs | "foobar" | "foobar" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | strEmptyR | "foo" | "foo" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | strEmptyL | "foo" | "foo" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | strBothEmpty | "" | "" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | ropeEq | True | True | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | ropeNeq | False | False | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | lists | [1,2,3,4] | [1,2,3,4] | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | listEmptyR | [1,2] | [1,2] | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | listEmptyL | [1,2] | [1,2] | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | listBothEmpty | [] | [] | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | chunkAppend | [2,4,6,1] | [2,4,6,1] | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | nested | "abcdef" | "abcdef" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | polyStr | "hihi" | "hihi" | agree | t_elm_AppendTypeSplitTest (native) |
| AppendTypeSplitTest | polyList | [7,7] | [7,7] | agree | t_elm_AppendTypeSplitTest (native) |
| AstralCharCasePatternTest | a | "other" | "other" | agree | t_elm_AstralCharCasePatternTest |
| AstralCharCasePatternTest | euro | "euro" | "euro" | agree | t_elm_AstralCharCasePatternTest |
| AstralCharCasePatternTest | escape | "grin" | "grin" | agree | t_elm_AstralCharCasePatternTest |
| AstralCharCasePatternTest | literal | "grin" | "grin" | agree | t_elm_AstralCharCasePatternTest |
| AstralCharLiteralTest | astral | 128512 | 128512 | agree | t_elm_AstralCharLiteralTest |
| AstralCharLiteralTest | bmp | 8364 | 8364 | agree | t_elm_AstralCharLiteralTest |
| AstralCharLiteralTest | sameAsWritten | True | True | agree | t_elm_AstralCharLiteralTest |
| BoolAndTest | and1 | True | True | agree | t_elm_BoolAndTest |
| BoolAndTest | and2 | False | False | agree | t_elm_BoolAndTest |
| BoolAndTest | and3 | False | False | agree | t_elm_BoolAndTest |
| BoolAndTest | and4 | False | False | agree | t_elm_BoolAndTest |
| BoolOrTest | or1 | True | True | agree | t_elm_BoolOrTest |
| BoolOrTest | or2 | True | True | agree | t_elm_BoolOrTest |
| BoolOrTest | or3 | True | True | agree | t_elm_BoolOrTest |
| BoolOrTest | or4 | False | False | agree | t_elm_BoolOrTest |
| BoolShortCircuitParserIdiomTest | peek at past-end | "none" | "none" | agree | t_elm_BoolShortCircuitParserIdiomTest (native) |
| BoolShortCircuitParserIdiomTest | peek at first | 'H' | 'H' | agree | t_elm_BoolShortCircuitParserIdiomTest (native) |
| BoolShortCircuitTest | shortAnd | False | False | agree | t_elm_BoolShortCircuitTest |
| BoolShortCircuitTest | shortOr | True | True | agree | t_elm_BoolShortCircuitTest |
| CapturedStagedFuncCallTest | direct | 15 | 15 | agree | t_elm_CapturedStagedFuncCallTest |
| CapturedStagedFuncCallTest | viaCapture | 15 | 15 | agree | t_elm_CapturedStagedFuncCallTest |
| CaseAsPatternTest | as1 | 0 | 0 | agree | t_elm_CaseAsPatternTest |
| CaseAsPatternTest | as2 | 3 | 3 | agree | t_elm_CaseAsPatternTest |
| CaseAsPatternTest | as3 | 6 | 6 | agree | t_elm_CaseAsPatternTest |
| CaseBoolTest | case1 | "yes" | "yes" | agree | t_elm_CaseBoolTest |
| CaseBoolTest | case2 | "no" | "no" | agree | t_elm_CaseBoolTest |
| CaseBranchSelectionTest | classify | ["zero","one","pair 2 3","other 9"] | ["zero","one","pair 2 3","other 9"] | agree | t_elm_CaseBranchSelectionTest (native) |
| CaseBranchSelectionTest | first match wins | "specific" | "specific" | agree | t_elm_CaseBranchSelectionTest (native) |
| CaseCharManyBranchTest | d0 | 0 | 0 | agree | t_elm_CaseCharManyBranchTest |
| CaseCharManyBranchTest | d5 | 5 | 5 | agree | t_elm_CaseCharManyBranchTest |
| CaseCharManyBranchTest | d9 | 9 | 9 | agree | t_elm_CaseCharManyBranchTest |
| CaseCharManyBranchTest | other | -1 | -1 | agree | t_elm_CaseCharManyBranchTest |
| CaseCharTest | char1 | "vowel a" | "vowel a" | agree | t_elm_CaseCharTest |
| CaseCharTest | char2 | "vowel e" | "vowel e" | agree | t_elm_CaseCharTest |
| CaseCharTest | char3 | "other" | "other" | agree | t_elm_CaseCharTest |
| CaseCharTest | char4 | "other" | "other" | agree | t_elm_CaseCharTest |
| CaseCtorArgPatternTest | id | 30 | 30 | agree | t_elm_CaseCtorArgPatternTest |
| CaseCtorArgPatternTest | age | 25 | 25 | agree | t_elm_CaseCtorArgPatternTest |
| CaseCustomType4Test | dir1 | "up" | "up" | agree | t_elm_CaseCustomType4Test |
| CaseCustomType4Test | dir2 | "down" | "down" | agree | t_elm_CaseCustomType4Test |
| CaseCustomType4Test | dir3 | "left" | "left" | agree | t_elm_CaseCustomType4Test |
| CaseCustomType4Test | dir4 | "right" | "right" | agree | t_elm_CaseCustomType4Test |
| CaseCustomType4WildcardTest | card1 | "hearts" | "hearts" | agree | t_elm_CaseCustomType4WildcardTest |
| CaseCustomType4WildcardTest | card2 | "spades" | "spades" | agree | t_elm_CaseCustomType4WildcardTest |
| CaseCustomType4WildcardTest | card3 | "other" | "other" | agree | t_elm_CaseCustomType4WildcardTest |
| CaseCustomType4WildcardTest | card4 | "other" | "other" | agree | t_elm_CaseCustomType4WildcardTest |
| CaseCustomTypeTest | shape1 | 100 | 100 | agree | t_elm_CaseCustomTypeTest |
| CaseCustomTypeTest | shape2 | 50 | 50 | agree | t_elm_CaseCustomTypeTest |
| CaseDeepNestTest | r1 | "x=0,y=0" | "x=0,y=0" | agree | t_elm_CaseDeepNestTest |
| CaseDeepNestTest | r2 | "x=0,y=other" | "x=0,y=other" | agree | t_elm_CaseDeepNestTest |
| CaseDeepNestTest | r3 | "x=1,y=0" | "x=1,y=0" | agree | t_elm_CaseDeepNestTest |
| CaseDeepNestTest | r4 | "x=other" | "x=other" | agree | t_elm_CaseDeepNestTest |
| CaseDeepNestTest | triple | "all zero" | "all zero" | agree | t_elm_CaseDeepNestTest |
| CaseDeepNestTest | triple2 | "z=other" | "z=other" | agree | t_elm_CaseDeepNestTest |
| CaseDeeplyNestedTest | deep1 | "all" | "all" | agree | t_elm_CaseDeeplyNestedTest |
| CaseDeeplyNestedTest | deep2 | "two" | "two" | agree | t_elm_CaseDeeplyNestedTest |
| CaseDefaultTest | default1 | "special" | "special" | agree | t_elm_CaseDefaultTest |
| CaseDefaultTest | default2 | "normal" | "normal" | agree | t_elm_CaseDefaultTest |
| CaseDefaultTest | default3 | "normal" | "normal" | agree | t_elm_CaseDefaultTest |
| CaseFanOutShadowTest | r1 | 5 | 5 | agree | t_elm_CaseFanOutShadowTest |
| CaseFanOutShadowTest | r2 | -1 | -1 | agree | t_elm_CaseFanOutShadowTest |
| CaseFanOutShadowTest | r3 | 0 | 0 | agree | t_elm_CaseFanOutShadowTest |
| CaseGuardLikeTest | grade1 | "A" | "A" | agree | t_elm_CaseGuardLikeTest |
| CaseGuardLikeTest | grade2 | "B" | "B" | agree | t_elm_CaseGuardLikeTest |
| CaseGuardLikeTest | grade3 | "C" | "C" | agree | t_elm_CaseGuardLikeTest |
| CaseGuardLikeTest | grade4 | "F" | "F" | agree | t_elm_CaseGuardLikeTest |
| CaseInLambdaTest | lambda1 | "yes" | "yes" | agree | t_elm_CaseInLambdaTest |
| CaseInLambdaTest | lambda2 | "no" | "no" | agree | t_elm_CaseInLambdaTest |
| CaseInLambdaTest | lambda3 | "yes" | "yes" | agree | t_elm_CaseInLambdaTest |
| CaseInLetTest | let1 | "positive" | "positive" | agree | t_elm_CaseInLetTest |
| CaseInLetTest | let2 | "zero" | "zero" | agree | t_elm_CaseInLetTest |
| CaseInLetTest | let3 | "negative" | "negative" | agree | t_elm_CaseInLetTest |
| CaseIntTest | case1 | "one" | "one" | agree | t_elm_CaseIntTest |
| CaseIntTest | case2 | "two" | "two" | agree | t_elm_CaseIntTest |
| CaseIntTest | case3 | "other" | "other" | agree | t_elm_CaseIntTest |
| CaseListConsTest | sum1 | 0 | 0 | agree | t_elm_CaseListConsTest |
| CaseListConsTest | sum2 | 1 | 1 | agree | t_elm_CaseListConsTest |
| CaseListConsTest | sum3 | 6 | 6 | agree | t_elm_CaseListConsTest |
| CaseListTest | case1 | "empty" | "empty" | agree | t_elm_CaseListTest |
| CaseListTest | case2 | "one" | "one" | agree | t_elm_CaseListTest |
| CaseListTest | case3 | "many" | "many" | agree | t_elm_CaseListTest |
| CaseListThreeWayTest | desc1 | "empty" | "empty" | agree | t_elm_CaseListThreeWayTest (native) |
| CaseListThreeWayTest | desc2 | "single: 42" | "single: 42" | agree | t_elm_CaseListThreeWayTest (native) |
| CaseListThreeWayTest | desc3 | "multiple: 1" | "multiple: 1" | agree | t_elm_CaseListThreeWayTest (native) |
| CaseManyBranchesTest | day1 | "Monday" | "Monday" | agree | t_elm_CaseManyBranchesTest |
| CaseManyBranchesTest | day5 | "Friday" | "Friday" | agree | t_elm_CaseManyBranchesTest |
| CaseManyBranchesTest | day7 | "Sunday" | "Sunday" | agree | t_elm_CaseManyBranchesTest |
| CaseMaybePairTest | both | 7 | 7 | agree | t_elm_CaseMaybePairTest |
| CaseMaybePairTest | first | 3 | 3 | agree | t_elm_CaseMaybePairTest |
| CaseMaybePairTest | second | 4 | 4 | agree | t_elm_CaseMaybePairTest |
| CaseMaybePairTest | neither | 0 | 0 | agree | t_elm_CaseMaybePairTest |
| CaseMaybeTest | case1 | 42 | 42 | agree | t_elm_CaseMaybeTest |
| CaseMaybeTest | case2 | -1 | -1 | agree | t_elm_CaseMaybeTest |
| CaseMixedPatternTest | head | 42 | 42 | agree | t_elm_CaseMixedPatternTest |
| CaseMixedPatternTest | empty | 0 | 0 | agree | t_elm_CaseMixedPatternTest |
| CaseMixedPatternTest | pair_head | 10 | 10 | agree | t_elm_CaseMixedPatternTest |
| CaseMixedPatternTest | pair_empty | -1 | -1 | agree | t_elm_CaseMixedPatternTest |
| CaseMixedPatternTest | nested | 99 | 99 | agree | t_elm_CaseMixedPatternTest |

Elm01: 40 programs, 130 checks, 130 agree.

## Elm02

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CaseMultiFieldExtractTest | point1 | 3 | 3 | agree | t_elm_CaseMultiFieldExtractTest |
| CaseMultiFieldExtractTest | point2 | 6 | 6 | agree | t_elm_CaseMultiFieldExtractTest |
| CaseMultiFieldExtractTest | rect1 | 50 | 50 | agree | t_elm_CaseMultiFieldExtractTest |
| CaseNestedCtorTest | single | 42 | 42 | agree | t_elm_CaseNestedCtorTest |
| CaseNestedCtorTest | double | 3 | 3 | agree | t_elm_CaseNestedCtorTest |
| CaseNestedRecordAccessTest | test1 | True | True | agree | t_elm_CaseNestedRecordAccessTest |
| CaseNestedRecordAccessTest | test2 | False | False | agree | t_elm_CaseNestedRecordAccessTest |
| CaseNestedRecordAccessTest | test3 | True | True | agree | t_elm_CaseNestedRecordAccessTest |
| CaseNestedRecordAccessTest | test4 | True | True | agree | t_elm_CaseNestedRecordAccessTest |
| CaseNestedTest | nested1 | "both" | "both" | agree | t_elm_CaseNestedTest |
| CaseNestedTest | nested2 | "first" | "first" | agree | t_elm_CaseNestedTest |
| CaseNestedTest | nested3 | "second" | "second" | agree | t_elm_CaseNestedTest |
| CaseNestedTest | nested4 | "neither" | "neither" | agree | t_elm_CaseNestedTest |
| CaseOrderTest | ord1 | "less" | "less" | agree | t_elm_CaseOrderTest |
| CaseOrderTest | ord2 | "equal" | "equal" | agree | t_elm_CaseOrderTest |
| CaseOrderTest | ord3 | "greater" | "greater" | agree | t_elm_CaseOrderTest |
| CaseResultTest | res1 | 42 | 42 | agree | t_elm_CaseResultTest |
| CaseResultTest | res2 | -1 | -1 | agree | t_elm_CaseResultTest |
| CaseResultTest | res3 | 100 | 100 | agree | t_elm_CaseResultTest |
| CaseReturnFunctionTest | op1 | 7 | 7 | agree | t_elm_CaseReturnFunctionTest |
| CaseReturnFunctionTest | op2 | 3 | 3 | agree | t_elm_CaseReturnFunctionTest |
| CaseReturnFunctionTest | op3 | 10 | 10 | agree | t_elm_CaseReturnFunctionTest |
| CaseReturningLambdaTest | r1 | 6 | 6 | agree | t_elm_CaseReturningLambdaTest |
| CaseReturningLambdaTest | r2 | 5 | 5 | agree | t_elm_CaseReturningLambdaTest |
| CaseReturningLambdaTest | r3 | 0 | 0 | agree | t_elm_CaseReturningLambdaTest |
| CaseReturningLambdaTest | r4 | 99 | 99 | agree | t_elm_CaseReturningLambdaTest |
| CaseSharedBranchTest | r1 | "greeting" | "greeting" | agree | t_elm_CaseSharedBranchTest |
| CaseSharedBranchTest | r2 | "farewell" | "farewell" | agree | t_elm_CaseSharedBranchTest |
| CaseSharedBranchTest | r3 | "unknown cmd" | "unknown cmd" | agree | t_elm_CaseSharedBranchTest |
| CaseSharedBranchTest | r4 | "fixed" | "fixed" | agree | t_elm_CaseSharedBranchTest |
| CaseSingleCtorBoolMultiTypeTest | nested_true | "split" | "split" | agree | t_elm_CaseSingleCtorBoolMultiTypeTest |
| CaseSingleCtorBoolMultiTypeTest | nested_false | "join" | "join" | agree | t_elm_CaseSingleCtorBoolMultiTypeTest |
| CaseSingleCtorBoolMultiTypeTest | extract_true | True | True | agree | t_elm_CaseSingleCtorBoolMultiTypeTest |
| CaseSingleCtorBoolMultiTypeTest | extract_false | False | False | agree | t_elm_CaseSingleCtorBoolMultiTypeTest |
| CaseSingleCtorBoolMultiTypeTest | wrap_int | 42 | 42 | agree | t_elm_CaseSingleCtorBoolMultiTypeTest |
| CaseSingleCtorBoolTest | nested_true | "split" | "split" | agree | t_elm_CaseSingleCtorBoolTest |
| CaseSingleCtorBoolTest | nested_false | "join" | "join" | agree | t_elm_CaseSingleCtorBoolTest |
| CaseSingleCtorBoolTest | extract_true | True | True | agree | t_elm_CaseSingleCtorBoolTest |
| CaseSingleCtorBoolTest | extract_false | False | False | agree | t_elm_CaseSingleCtorBoolTest |
| CaseStringEmptyPatternTest | empty | "yes" | "yes" | agree | t_elm_CaseStringEmptyPatternTest |
| CaseStringEmptyPatternTest | Y | "yes" | "yes" | agree | t_elm_CaseStringEmptyPatternTest |
| CaseStringEmptyPatternTest | y | "yes" | "yes" | agree | t_elm_CaseStringEmptyPatternTest |
| CaseStringEmptyPatternTest | n | "no" | "no" | agree | t_elm_CaseStringEmptyPatternTest |
| CaseStringEmptyPatternTest | maybe | "retry" | "retry" | agree | t_elm_CaseStringEmptyPatternTest |
| CaseStringEscapeTest | esc1 | "newline" | "newline" | agree | t_elm_CaseStringEscapeTest |
| CaseStringEscapeTest | esc2 | "tab" | "tab" | agree | t_elm_CaseStringEscapeTest |
| CaseStringEscapeTest | esc3 | "quote" | "quote" | agree | t_elm_CaseStringEscapeTest |
| CaseStringEscapeTest | esc4 | "other" | "other" | agree | t_elm_CaseStringEscapeTest |
| CaseStringManyBranchTest | d1 | "Monday" | "Monday" | agree | t_elm_CaseStringManyBranchTest |
| CaseStringManyBranchTest | d4 | "Thursday" | "Thursday" | agree | t_elm_CaseStringManyBranchTest |
| CaseStringManyBranchTest | d7 | "Sunday" | "Sunday" | agree | t_elm_CaseStringManyBranchTest |
| CaseStringManyBranchTest | other | "unknown" | "unknown" | agree | t_elm_CaseStringManyBranchTest |
| CaseStringTest | case1 | 1 | 1 | agree | t_elm_CaseStringTest |
| CaseStringTest | case2 | 2 | 2 | agree | t_elm_CaseStringTest |
| CaseStringTest | case3 | 0 | 0 | agree | t_elm_CaseStringTest |
| CaseTreeTest | tree1 | 0 | 0 | agree | t_elm_CaseTreeTest |
| CaseTreeTest | tree2 | 1 | 1 | agree | t_elm_CaseTreeTest |
| CaseTreeTest | tree3 | 3 | 3 | agree | t_elm_CaseTreeTest |
| CaseTripleTest | triple1 | "all zero" | "all zero" | agree | t_elm_CaseTripleTest |
| CaseTripleTest | triple2 | "x zero" | "x zero" | agree | t_elm_CaseTripleTest |
| CaseTripleTest | triple3 | "z zero" | "z zero" | agree | t_elm_CaseTripleTest |
| CaseTripleTest | triple4 | "none zero" | "none zero" | agree | t_elm_CaseTripleTest |
| CaseTupleLiteralTest | origin | "origin" | "origin" | agree | t_elm_CaseTupleLiteralTest |
| CaseTupleLiteralTest | xaxis | "x-axis" | "x-axis" | agree | t_elm_CaseTupleLiteralTest |
| CaseTupleLiteralTest | yaxis | "y-axis" | "y-axis" | agree | t_elm_CaseTupleLiteralTest |
| CaseTupleLiteralTest | unit | "unit" | "unit" | agree | t_elm_CaseTupleLiteralTest |
| CaseTupleLiteralTest | general | "general" | "general" | agree | t_elm_CaseTupleLiteralTest |
| CaseTupleTest | pair1 | "both zero" | "both zero" | agree | t_elm_CaseTupleTest |
| CaseTupleTest | pair2 | "x is zero" | "x is zero" | agree | t_elm_CaseTupleTest |
| CaseTupleTest | pair3 | "y is zero" | "y is zero" | agree | t_elm_CaseTupleTest |
| CaseTupleTest | pair4 | "neither zero" | "neither zero" | agree | t_elm_CaseTupleTest |
| CaseUnicodeCharTest | char1 | "greek alpha" | "greek alpha" | agree | t_elm_CaseUnicodeCharTest |
| CaseUnicodeCharTest | char2 | "greek beta" | "greek beta" | agree | t_elm_CaseUnicodeCharTest |
| CaseUnicodeCharTest | char3 | "cjk" | "cjk" | agree | t_elm_CaseUnicodeCharTest |
| CaseUnicodeCharTest | char4 | "other" | "other" | agree | t_elm_CaseUnicodeCharTest |
| CharAstralClosureCaptureTest | cap_add | [128513,98] | [128513,98] | agree | t_elm_CharAstralClosureCaptureTest |
| CharAstralClosureCaptureTest | cap_return | [128512,119070] | [128512,119070] | agree | t_elm_CharAstralClosureCaptureTest |
| CharAstralClosureCaptureTest | pap_pairs | [128513,128514] | [128513,128514] | agree | t_elm_CharAstralClosureCaptureTest |
| CharAstralCustomFieldTest | box_code | 128512 | 128512 | agree | t_elm_CharAstralCustomFieldTest |
| CharAstralCustomFieldTest | shape_codes | [128512,119070,-1] | [128512,119070,-1] | agree | t_elm_CharAstralCustomFieldTest |
| CharAstralRecordFieldTest | rec_c | 128512 | 128512 | agree | t_elm_CharAstralRecordFieldTest |
| CharAstralRecordFieldTest | rec_n | 7 | 7 | agree | t_elm_CharAstralRecordFieldTest |
| CharAstralRecordFieldTest | rec_updated | 119070 | 119070 | agree | t_elm_CharAstralRecordFieldTest |
| CharAstralRecordFieldTest | rec_eq | True | True | agree | t_elm_CharAstralRecordFieldTest |
| CharAstralTupleTest | tup2_code | 128512 | 128512 | agree | t_elm_CharAstralTupleTest |
| CharAstralTupleTest | tup3_code | 119070 | 119070 | agree | t_elm_CharAstralTupleTest |
| CharCaptureEscapedTailDefTest | hit | True | True | agree | t_elm_CharCaptureEscapedTailDefTest |
| CharCaptureEscapedTailDefTest | miss | False | False | agree | t_elm_CharCaptureEscapedTailDefTest |
| CharCaptureEscapedTailDefTest | both | True | True | agree | t_elm_CharCaptureEscapedTailDefTest |
| CharCasePredicateTest | result | "comma" | "comma" | agree | t_elm_CharCasePredicateTest |
| CharLiteralPatternMatchMinimalTest | m1_bareChar | "y" | "y" | agree | t_elm_CharLiteralPatternMatchMinimalTest |
| CharLiteralPatternMatchMinimalTest | m2_charInTuple | "y" | "y" | agree | t_elm_CharLiteralPatternMatchMinimalTest |
| CharLiteralPatternMatchMinimalTest | m3_charInMaybe | "y" | "y" | agree | t_elm_CharLiteralPatternMatchMinimalTest |
| CharLiteralPatternMatchMinimalTest | m4_charInMaybeTuple | "y" | "y" | agree | t_elm_CharLiteralPatternMatchMinimalTest |
| CharLiteralPatternMatchVariousTest | dquote | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | lbrace | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | lowerA | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | backslash | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | newline | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | digit0 | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharLiteralPatternMatchVariousTest | space | "y" | "y" | agree | t_elm_CharLiteralPatternMatchVariousTest |
| CharUnicodeTest | code1 | 955 | 955 | agree | t_elm_CharUnicodeTest |
| CharUnicodeTest | code2 | 8364 | 8364 | agree | t_elm_CharUnicodeTest |
| ClosureCapture01Test | unwrap1 | 42 | 42 | agree | t_elm_ClosureCapture01Test |
| ClosureCapture01Test | unwrap2 | 99 | 99 | agree | t_elm_ClosureCapture01Test |
| ClosureCapture02Test | just | "hello" | "hello" | agree | t_elm_ClosureCapture02Test |
| ClosureCapture02Test | nothing | "none" | "none" | agree | t_elm_ClosureCapture02Test |
| ClosureCapture03Test | ok | 42 | 42 | agree | t_elm_ClosureCapture03Test |
| ClosureCapture03Test | err | -1 | -1 | agree | t_elm_ClosureCapture03Test |
| ClosureCapture04Test | both | 30 | 30 | agree | t_elm_ClosureCapture04Test |
| ClosureCapture04Test | first | 10 | 10 | agree | t_elm_ClosureCapture04Test |
| ClosureCapture04Test | neither | 0 | 0 | agree | t_elm_ClosureCapture04Test |
| ClosureCapture05Test | both | "ab" | "ab" | agree | t_elm_ClosureCapture05Test |
| ClosureCapture05Test | one | "a" | "a" | agree | t_elm_ClosureCapture05Test |
| ClosureCapture05Test | none | "" | "" | agree | t_elm_ClosureCapture05Test |
| ClosureCapture06Test | both | "ab" | "ab" | agree | t_elm_ClosureCapture06Test |
| ClosureCapture06Test | one | "a" | "a" | agree | t_elm_ClosureCapture06Test |
| ClosureCapture06Test | none | "" | "" | agree | t_elm_ClosureCapture06Test |
| ClosureCaptureBoolTest | when_true | 1 | 1 | agree | t_elm_ClosureCaptureBoolTest |
| ClosureCaptureBoolTest | when_false | 0 | 0 | agree | t_elm_ClosureCaptureBoolTest |
| ClosureCaptureRecordTest | rec | 6 | 6 | agree | t_elm_ClosureCaptureRecordTest |
| ClosureCaptureRecordTest | tup | 6 | 6 | agree | t_elm_ClosureCaptureRecordTest |
| ClosureCaptureTupleTest | add | 6 | 6 | agree | t_elm_ClosureCaptureTupleTest |
| ClosureCaptureTupleTest | nested | 10 | 10 | agree | t_elm_ClosureCaptureTupleTest |
| ClosureCaptureTupleTest | mixed | 9 | 9 | agree | t_elm_ClosureCaptureTupleTest |
| ClosureDifferentClosuresPerIfBranchInsideACaseTest | testValue | 20 | 20 | agree | t_elm_ClosureDifferentClosuresPerIfBranchInsideACaseTest |
| CombinatorBComposeTest | result | 25 | 25 | agree | t_elm_CombinatorBComposeTest |

Elm02: 40 programs, 127 checks, 127 agree.

## Elm03

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CombinatorBSumMapTest | result | 9 | 9 | agree | t_elm_CombinatorBSumMapTest |
| CombinatorCConsTest | result | [1,2,3] | [1,2,3] | agree | t_elm_CombinatorCConsTest |
| CombinatorCFlipTest | result | -7 | -7 | agree | t_elm_CombinatorCFlipTest |
| CombinatorIIdentityTest | result | 42 | 42 | agree | t_elm_CombinatorIIdentityTest |
| CombinatorListStringTest | b_sum_map | 9 | 9 | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | sp_mul | 84 | 84 | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | w_concat | "hihi" | "hihi" | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | c_cons | [1,2,3] | [1,2,3] | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | s_palindrome | "strawstraw!" | "strawstraw!" | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | t_pipe | 12 | 12 | agree | t_elm_CombinatorListStringTest |
| CombinatorListStringTest | p_lengths | 5 | 5 | agree | t_elm_CombinatorListStringTest |
| CombinatorPLengthsTest | result | 5 | 5 | agree | t_elm_CombinatorPLengthsTest |
| CombinatorRefIdentityBugTest | b_compose | 25 | 25 | agree | t_elm_CombinatorRefIdentityBugTest |
| CombinatorRefIdentityBugTest | s_feed | 15 | 15 | agree | t_elm_CombinatorRefIdentityBugTest |
| CombinatorSFeedTest | result | 15 | 15 | agree | t_elm_CombinatorSFeedTest |
| CombinatorSPalindromeTest | result | "strawstraw!" | "strawstraw!" | agree | t_elm_CombinatorSPalindromeTest |
| CombinatorSpCombineTest | result | 84 | 84 | agree | t_elm_CombinatorSpCombineTest |
| CombinatorSpMulTest | result | 84 | 84 | agree | t_elm_CombinatorSpMulTest |
| CombinatorStdlibTCombinatorPipeListIntoComposedOpsTest | testValue | 12 | 12 | agree | t_elm_CombinatorStdlibTCombinatorPipeListIntoComposedOpsTest |
| CombinatorTPipeTest | result | 12 | 12 | agree | t_elm_CombinatorTPipeTest |
| CombinatorTThrushTest | result | 21 | 21 | agree | t_elm_CombinatorTThrushTest |
| CombinatorTest | b_compose | 25 | 25 | agree | t_elm_CombinatorTest |
| CombinatorTest | c_flip | -7 | -7 | agree | t_elm_CombinatorTest |
| CombinatorTest | s_feed | 15 | 15 | agree | t_elm_CombinatorTest |
| CombinatorTest | sp_combine | 84 | 84 | agree | t_elm_CombinatorTest |
| CombinatorTest | w_dup | 81 | 81 | agree | t_elm_CombinatorTest |
| CombinatorTest | t_thrush | 21 | 21 | agree | t_elm_CombinatorTest |
| CombinatorTest | i_identity | 42 | 42 | agree | t_elm_CombinatorTest |
| CombinatorWConcatTest | result | "hihi" | "hihi" | agree | t_elm_CombinatorWConcatTest |
| CombinatorWDupTest | result | 81 | 81 | agree | t_elm_CombinatorWDupTest |
| CompilerIssue1766LetMutualRecursionMismatchTest | result | Goal | Goal | agree | t_elm_CompilerIssue1766LetMutualRecursionMismatchTest |
| CompilerIssue1793ComparableTupleLetCrashTest | f 1 | True | True | agree | t_elm_CompilerIssue1793ComparableTupleLetCrashTest |
| CompilerIssue1813TcoClosureCapturesMutatedArgTest | results | [1,2,3] | [1,2,3] | agree | t_elm_CompilerIssue1813TcoClosureCapturesMutatedArgTest |
| CompilerIssue1858AnnotatedPolymorphicRecursionTest | bVals | Just "b" | Just "b" | agree | t_elm_CompilerIssue1858AnnotatedPolymorphicRecursionTest |
| CompilerIssue1890RecordUpdateMutualRecursionCrashTest | result | { x = (), y = () } | { x = (), y = () } | agree | t_elm_CompilerIssue1890RecordUpdateMutualRecursionCrashTest |
| CompilerIssue1916PhantomExtensibleAliasCrashTest | bug | () | () | agree | t_elm_CompilerIssue1916PhantomExtensibleAliasCrashTest |
| CompilerIssue1964AnnotatedPolymorphicRecursionWrapperTest | depth | 2 | 2 | agree | t_elm_CompilerIssue1964AnnotatedPolymorphicRecursionWrapperTest |
| CompilerIssue2017TcoContinuationShadowedTest | windDown | 1 | 1 | agree | t_elm_CompilerIssue2017TcoContinuationShadowedTest |
| CompilerIssue2019AliasOfTypeVariableTest | test | 1 | 1 | agree | t_elm_CompilerIssue2019AliasOfTypeVariableTest |
| CompilerIssue2057CallSiteChangesInferredTypeTest | sort | [] | [] | agree | t_elm_CompilerIssue2057CallSiteChangesInferredTypeTest |
| CompilerIssue2119MutualRecursionUnannotatedTest | depth | 1 | 1 | agree | t_elm_CompilerIssue2119MutualRecursionUnannotatedTest |
| CompilerIssue2207MutualRecursionSecondFunctionTest | g 3 | 0 | 0 | agree | t_elm_CompilerIssue2207MutualRecursionSecondFunctionTest |
| CompilerIssue2221TcoContinuationTest | g 5 | 120 | 120 | agree | t_elm_CompilerIssue2221TcoContinuationTest |
| CompilerIssue2252IdentityAliasTest | map | 3 | 3 | agree | t_elm_CompilerIssue2252IdentityAliasTest |
| CompilerIssue2268TcoClosureCaptureTest | plain | [3,2,1] | [3,2,1] | agree | t_elm_CompilerIssue2268TcoClosureCaptureTest |
| CompilerIssue2268TcoClosureCaptureTest | tco | [3,2,1] | [3,2,1] | agree | t_elm_CompilerIssue2268TcoClosureCaptureTest |
| CompilerIssue2298IdentityAliasResultTest | make | 7 | 7 | agree | t_elm_CompilerIssue2298IdentityAliasResultTest |
| CoreIssue988NanContainerSelfEqualityTest | record | False | False | agree | t_elm_CoreIssue988NanContainerSelfEqualityTest |
| CoreIssue988NanContainerSelfEqualityTest | custom type | False | False | agree | t_elm_CoreIssue988NanContainerSelfEqualityTest |
| CoreIssue988NanContainerSelfEqualityTest | maybe | False | False | agree | t_elm_CoreIssue988NanContainerSelfEqualityTest |
| CoreIssue988NanContainerSelfEqualityTest | shared inner tuple | False | False | agree | t_elm_CoreIssue988NanContainerSelfEqualityTest |
| CoreIssue988NanContainerSelfEqualityTest | shared inner list | False | False | agree | t_elm_CoreIssue988NanContainerSelfEqualityTest |
| CovEtaDebugLogTest | eta body | 7 | 7 | agree | t_elm_CovEtaDebugLogTest |
| CovForeignTypesTest | CovForeignTypesTest | 42 | 42 | agree | t_elm_CovForeignTypesTest |
| CovLambdaBoundaryCaseBoundaryInARecursiveValueTest | testValue | 4 | 4 | agree | t_elm_CovLambdaBoundaryCaseBoundaryInARecursiveValueTest |
| CovLambdaBoundaryCaseBoundaryUnderAFunctionAliasTest | testValue | 4 | 4 | agree | t_elm_CovLambdaBoundaryCaseBoundaryUnderAFunctionAliasTest |
| CovLambdaSetFunctionsInRecordsTuplesAndMaybeTest | testValue | 14 | 14 | agree | t_elm_CovLambdaSetFunctionsInRecordsTuplesAndMaybeTest |
| CovPatternSplitTupleAndConstructorParametersMatchedByCaseTest | testValue | <function> | <function> | agree | t_elm_CovPatternSplitTupleAndConstructorParametersMatchedByCaseTest (native) |

Elm03: 40 programs, 58 checks, 58 agree.

## Elm04

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CovPortIncomingArrayTest | testValue | 1 | 1 | agree | t_elm_CovPortIncomingArrayTest |
| CovPortIncomingJSONValueTest | testValue | 1 | 1 | agree | t_elm_CovPortIncomingJSONValueTest |
| CovPortIncomingTripleTest | testValue | 1 | 1 | agree | t_elm_CovPortIncomingTripleTest |
| CovPortIncomingUnitTest | testValue | 1 | 1 | agree | t_elm_CovPortIncomingUnitTest |
| CovPortOutgoingJSONValueTest | testValue | 1 | 1 | agree | t_elm_CovPortOutgoingJSONValueTest |
| CovPortOutgoingUnitTest | testValue | 1 | 1 | agree | t_elm_CovPortOutgoingUnitTest |
| CovTailRecPairParameterPassedUnchangedLetBoundAndRebuiltTest | testValue | <function> | <function> | agree | t_elm_CovTailRecPairParameterPassedUnchangedLetBoundAndRebuiltTest |
| CovTailRecPairParametersSwappedAndALoopReturningALambdaTest | testValue | <function> | <function> | agree | t_elm_CovTailRecPairParametersSwappedAndALoopReturningALambdaTest |
| CovTailRecSplitATripleParameterTest | testValue | <function> | <function> | agree | t_elm_CovTailRecSplitATripleParameterTest |
| CustomTypeFuncFieldTest | op1 | 11 | 11 | agree | t_elm_CustomTypeFuncFieldTest |
| CustomTypeFuncFieldTest | op2 | 20 | 20 | agree | t_elm_CustomTypeFuncFieldTest |
| CustomTypeMultiFieldTest | person | Person "Alice" 30 True | Person "Alice" 30 True | agree | t_elm_CustomTypeMultiFieldTest |
| CustomTypeNestedTest | nested | Node (Leaf 1) (Node (Leaf 2) (Leaf 3)) | Node (Leaf 1) (Node (Leaf 2) (Leaf 3)) | agree | t_elm_CustomTypeNestedTest |
| CustomTypePatternTest | name | "Alice" | "Alice" | agree | t_elm_CustomTypePatternTest |
| CustomTypePatternTest | age | 30 | 30 | agree | t_elm_CustomTypePatternTest |
| DebugLogLambdaBoundaryTest | DebugLogLambdaBoundaryTest | "hi" | "hi" | agree | t_elm_DebugLogLambdaBoundaryTest |
| DebugLogLambdaBoundaryTest | result | "hi" | "hi" | agree | t_elm_DebugLogLambdaBoundaryTest |
| DebugLogRecordTupleFieldTest | first | 1 | 1 | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugLogRecordTupleFieldTest | second | 2.5 | 2.5 | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugLogRecordTupleFieldTest | pair | (1,2.5) | (1,2.5) | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugLogRecordTupleFieldTest | x | 3 | 3 | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugLogRecordTupleFieldTest | y | 0.5 | 0.5 | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugLogRecordTupleFieldTest | point | (3,0.5,"p") | (3,0.5,"p") | agree | t_elm_DebugLogRecordTupleFieldTest |
| DebugNumberAtFloatTest | showAll | ["1.25","2.5"] | ["1.25","2.5"] | agree | t_elm_DebugNumberAtFloatTest (native) |
| DebugNumberAtFloatTest | bump | 3.5 | 3.5 | agree | t_elm_DebugNumberAtFloatTest (native) |
| DebugNumberAtFloatTest | bumpResult | 3.5 | 3.5 | agree | t_elm_DebugNumberAtFloatTest (native) |
| DebugNumberAtFloatTest | showAllInt | ["2","4"] | ["2","4"] | agree | t_elm_DebugNumberAtFloatTest (native) |
| DecisionTreeAdvancedDeepNestingWithFallbackTest | testValue | 5 | 5 | agree | t_elm_DecisionTreeAdvancedDeepNestingWithFallbackTest |
| DeepEqualityTest | nat 150 vs 200 | "False" | "False" | agree | t_elm_DeepEqualityTest (native) |
| DeepEqualityTest | nat 150 vs 150 | "True" | "True" | agree | t_elm_DeepEqualityTest (native) |
| DeepEqualityTest | nest 120 | "False" | "False" | agree | t_elm_DeepEqualityTest (native) |
| DeepEqualityTest | nest 500 /= | "True" | "True" | agree | t_elm_DeepEqualityTest (native) |
| DeepEqualityTest | record chain 300 | "False" | "False" | agree | t_elm_DeepEqualityTest (native) |
| DeepNestStressTest | nested_list | 1 | 1 | agree | t_elm_DeepNestStressTest |
| DeepNestStressTest | nested_tuple | 1 | 1 | agree | t_elm_DeepNestStressTest |
| DeepNestStressTest | nested_record | 1 | 1 | agree | t_elm_DeepNestStressTest |
| DeepNestStressTest | nested_let | 10 | 10 | agree | t_elm_DeepNestStressTest |
| DestructCaptureTest | captured | 56 | 56 | agree | t_elm_DestructCaptureTest |
| EdgeCaseAllDestructPatternsTest | testValue | [1,3,4,6] | [1,3,4,6] | agree | t_elm_EdgeCaseAllDestructPatternsTest |
| EitherTypeTest | left | 42 | 42 | agree | t_elm_EitherTypeTest |
| EitherTypeTest | right | 0 | 0 | agree | t_elm_EitherTypeTest |
| EitherTypeTest | mapLeft | 84 | 84 | agree | t_elm_EitherTypeTest |
| EitherTypeTest | isLeft | True | True | agree | t_elm_EitherTypeTest |
| EmbeddedEmptyStringCaptureTest | isEmpty | True | True | agree | t_elm_EmbeddedEmptyStringCaptureTest |
| EmbeddedEmptyStringCaptureTest | captured | "" | "" | agree | t_elm_EmbeddedEmptyStringCaptureTest |
| EmbeddedMixedConstantsTest | m | Nothing | Nothing | agree | t_elm_EmbeddedMixedConstantsTest |
| EmbeddedMixedConstantsTest | l | [] | [] | agree | t_elm_EmbeddedMixedConstantsTest |
| EmbeddedMixedConstantsTest | b | True | True | agree | t_elm_EmbeddedMixedConstantsTest |
| EmbeddedMixedConstantsTest | s | "" | "" | agree | t_elm_EmbeddedMixedConstantsTest |
| EmbeddedMixedConstantsTest | u | () | () | agree | t_elm_EmbeddedMixedConstantsTest |
| EmbeddedNilCaptureTest | result | "empty" | "empty" | agree | t_elm_EmbeddedNilCaptureTest |
| EmbeddedNilInCustomTypeTest | isEmpty | True | True | agree | t_elm_EmbeddedNilInCustomTypeTest |
| EmbeddedNilInCustomTypeTest | len | 0 | 0 | agree | t_elm_EmbeddedNilInCustomTypeTest |
| EmbeddedNilRecursiveTest | result | [2,4,6] | [2,4,6] | agree | t_elm_EmbeddedNilRecursiveTest |
| EmbeddedNothingCallbackTest | applied1 | Nothing | Nothing | agree | t_elm_EmbeddedNothingCallbackTest |
| EmbeddedNothingCallbackTest | applied2 | Just 11 | Just 11 | agree | t_elm_EmbeddedNothingCallbackTest |
| EmbeddedNothingCaptureTest | result | -1 | -1 | agree | t_elm_EmbeddedNothingCaptureTest |
| EmbeddedNothingInCustomTypeTest | result | -1 | -1 | agree | t_elm_EmbeddedNothingInCustomTypeTest |
| EmbeddedNothingInRecordTest | result | "nothing" | "nothing" | agree | t_elm_EmbeddedNothingInRecordTest |
| EmbeddedNothingInTupleTest | first | "nothing" | "nothing" | agree | t_elm_EmbeddedNothingInTupleTest |
| EmbeddedNothingInTupleTest | second | 42 | 42 | agree | t_elm_EmbeddedNothingInTupleTest |
| EmbeddedNothingMapTest | results | [-1,1,-1,2] | [-1,1,-1,2] | agree | t_elm_EmbeddedNothingMapTest |
| EmbeddedNothingPolymorphicTest | r1 | Nothing | Nothing | agree | t_elm_EmbeddedNothingPolymorphicTest |
| EmbeddedNothingPolymorphicTest | r2 | [] | [] | agree | t_elm_EmbeddedNothingPolymorphicTest |
| EmbeddedNothingPolymorphicTest | r3 | "" | "" | agree | t_elm_EmbeddedNothingPolymorphicTest |
| EmbeddedNothingRecursiveTest | find1 | Just 3 | Just 3 | agree | t_elm_EmbeddedNothingRecursiveTest |
| EmbeddedNothingRecursiveTest | find2 | Nothing | Nothing | agree | t_elm_EmbeddedNothingRecursiveTest |
| EmbeddedReturnNilTest | r1 | [2,4] | [2,4] | agree | t_elm_EmbeddedReturnNilTest |
| EmbeddedReturnNilTest | r2 | [] | [] | agree | t_elm_EmbeddedReturnNilTest |
| EmbeddedReturnNothingTest | r1 | 5 | 5 | agree | t_elm_EmbeddedReturnNothingTest |
| EmbeddedReturnNothingTest | r2 | -1 | -1 | agree | t_elm_EmbeddedReturnNothingTest |
| EmbeddedUnitCaptureTest | first | () | () | agree | t_elm_EmbeddedUnitCaptureTest |
| EmbeddedUnitCaptureTest | second | 42 | 42 | agree | t_elm_EmbeddedUnitCaptureTest |
| EntryMainOfRootModuleTest | which | "root" | "helper" or "root" | agree | t_elm_EntryMainOfRootModuleTest |
| EntryMainOfRootModuleTest | greeting | "hello" | "hello" | agree | t_elm_EntryMainOfRootModuleTest |
| EqualityStringChainCaseTest | case1 | "matched foo+True" | "matched foo+True" | agree | t_elm_EqualityStringChainCaseTest |
| EqualityStringChainCaseTest | case2 | "matched bar+False" | "matched bar+False" | agree | t_elm_EqualityStringChainCaseTest |
| EqualityStringChainCaseTest | case3 | "other" | "other" | agree | t_elm_EqualityStringChainCaseTest |
| EqualityStringChainCaseTest | eq1 | True | True | agree | t_elm_EqualityStringChainCaseTest |
| EqualityStringChainCaseTest | eq2 | False | False | agree | t_elm_EqualityStringChainCaseTest |

Elm04: 40 programs, 80 checks, 80 agree.

## Elm05

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| ErasedListSpecializationTest | n | 2 | 2 | agree | t_elm_ErasedListSpecializationTest |
| ErasedListSpecializationTest | m | 3 | 3 | agree | t_elm_ErasedListSpecializationTest |
| EscapeCustomCaseScrutineeTest | just | 7 | 7 | agree | t_elm_EscapeCustomCaseScrutineeTest |
| EscapeCustomCaseScrutineeTest | nothing | 0 | 0 | agree | t_elm_EscapeCustomCaseScrutineeTest |
| EscapeTopLevelTupleTest | a | 11 | 11 | agree | t_elm_EscapeTopLevelTupleTest |
| EscapeTopLevelTupleTest | b | 22 | 22 | agree | t_elm_EscapeTopLevelTupleTest |
| EtaExpandStateFunctionSequenceTest | testValue | 0 | 0 | agree | t_elm_EtaExpandStateFunctionSequenceTest |
| EtaExpandStateTest | r | [30,42,54] | [30,42,54] | agree | t_elm_EtaExpandStateTest |
| File | compiled | True | True | agree | t_elm_File |
| FlipFunctionTest | result | 3.14 | 3.14 | agree | t_elm_FlipFunctionTest |
| FloatEdgeTest | round 2.5 | "3" | "3" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | round -2.5 | "-2" | "-2" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | round 0.5 | "1" | "1" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | round -0.5 | "0" | "0" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | round 1.5 | "2" | "2" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | round -1.5 | "-1" | "-1" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | nan == nan | "False" | "False" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | nan /= nan | "True" | "True" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | 1 /= nan | "True" | "True" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | min 1 nan is NaN | "True" | "True" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | min 1 nan | "NaN" | "NaN" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | compare nan 1 | "GT" | "GT" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | foldl min is NaN | "True" | "True" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | foldl min | "NaN" | "NaN" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | map round | "[-2,0,3]" | "[-2,0,3]" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | case compare nan 1 | "GT" | "GT" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | case compare 1 2 | "LT" | "LT" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | case compare 2 2 | "EQ" | "EQ" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | compare tuple nan | "GT" | "GT" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | compare list nan | "GT" | "GT" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | just nan == just nan | "False" | "False" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | list nan /= list nan | "True" | "True" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | truncate nan | "0" | "0" | agree | t_elm_FloatEdgeTest (native) |
| FloatEdgeTest | pow 3 33 | "5559060566555523" | "5559060566555523" | agree | t_elm_FloatEdgeTest (native) |
| FunctionAccumulatorFunctionLookupTest | testValue | 15 | 15 | agree | t_elm_FunctionAccumulatorFunctionLookupTest |
| FunctionBasicTest | add1 | 5 | 5 | agree | t_elm_FunctionBasicTest |
| FunctionBasicTest | double1 | 10 | 10 | agree | t_elm_FunctionBasicTest |
| FunctionBasicTest | identity1 | 42 | 42 | agree | t_elm_FunctionBasicTest |
| FunctionChainedPartialApplicationTest | testValue | <function> | <function> | agree | t_elm_FunctionChainedPartialApplicationTest |
| FunctionCompappendWithStringTest | testValue | "helloworld" | "helloworld" | agree | t_elm_FunctionCompappendWithStringTest |
| FunctionMultiArgTest | three | 6 | 6 | agree | t_elm_FunctionMultiArgTest |
| FunctionMultiArgTest | four | 10 | 10 | agree | t_elm_FunctionMultiArgTest |
| FunctionMultiArgTest | five | 15 | 15 | agree | t_elm_FunctionMultiArgTest |
| FunctionUnannotatedCompappendTest | testValue | 0 | 0 | agree | t_elm_FunctionUnannotatedCompappendTest |
| FunctionValueChoiceTest | chooseIf called | 12 | 12 | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseIf folded | 6 | 6 | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseElse called | -1 | -1 | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseElse folded | 2 | 2 | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseC then | 7 | 7 | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseC else | (4,3) | (4,3) | agree | t_elm_FunctionValueChoiceTest |
| FunctionValueChoiceTest | chooseC sum | 17 | 17 | agree | t_elm_FunctionValueChoiceTest |
| HOParamApplyTwoTest | result | 1 | 1 | agree | t_elm_HOParamApplyTwoTest |
| HelloTest | HelloTest | "hello" | "hello" | agree | t_elm_HelloTest |
| HeteroClosureIntFloatTest | hetero_true | 13 | 13 | agree | t_elm_HeteroClosureIntFloatTest (native) |
| HeteroClosureIntFloatTest | hetero_false | 10 | 10 | agree | t_elm_HeteroClosureIntFloatTest (native) |
| HigherOrderFilterLikeFunctionTest | testValue | [1] | [1] | agree | t_elm_HigherOrderFilterLikeFunctionTest |
| HigherOrderFunctionChosenByIfTest | testValue | 2 | 2 | agree | t_elm_HigherOrderFunctionChosenByIfTest |
| HigherOrderFunctionFactoryTest | testValue | (5,2) | (5,2) | agree | t_elm_HigherOrderFunctionFactoryTest |
| HigherOrderReturnLambdaBasedOnConditionTest | testValue | 42 | 42 | agree | t_elm_HigherOrderReturnLambdaBasedOnConditionTest |
| HigherOrderTest | apply1 | 10 | 10 | agree | t_elm_HigherOrderTest |
| HigherOrderTest | apply2 | 25 | 25 | agree | t_elm_HigherOrderTest |
| HigherOrderTest | twice1 | 20 | 20 | agree | t_elm_HigherOrderTest |
| HigherOrderTripleNestedFunctionTest | testValue | [1,2,3] | [1,2,3] | agree | t_elm_HigherOrderTripleNestedFunctionTest |
| HoleyAliasTwoParamsTest | pairInt | 42 | 42 | agree | t_elm_HoleyAliasTwoParamsTest |
| HoleyAliasTwoParamsTest | pairStr | "hi" | "hi" | agree | t_elm_HoleyAliasTwoParamsTest |
| HoleyAliasTwoParamsTest | recFloat | 2.5 | 2.5 | agree | t_elm_HoleyAliasTwoParamsTest |
| HoleyAliasTwoParamsTest | recInt | 7 | 7 | agree | t_elm_HoleyAliasTwoParamsTest |
| HoleyAliasTwoParamsTest | box | Box (42,"hi") | Box (42,"hi") | agree | t_elm_HoleyAliasTwoParamsTest |
| HoleyAliasTwoParamsTest | rbox | RBox { first = 7, second = 2.5 } | RBox { first = 7, second = 2.5 } | agree | t_elm_HoleyAliasTwoParamsTest |
| ImportClosedTypeOpenItemTest | closed | 9 | 9 | agree | t_elm_ImportClosedTypeOpenItemTest |
| ImportExposingAllTest | all | [42,101,7,3] | [42,101,7,3] | agree | t_elm_ImportExposingAllTest |
| ImportExposingItemsTest | double | 42 | 42 | agree | t_elm_ImportExposingItemsTest |
| ImportExposingItemsTest | open | [0,7] | [0,7] | agree | t_elm_ImportExposingItemsTest |
| ImportExposingItemsTest | point | 3 | 3 | agree | t_elm_ImportExposingItemsTest |
| ImportExposingItemsTest | closed | 5 | 5 | agree | t_elm_ImportExposingItemsTest |
| ImportExposingItemsTest | qualified | 101 | 101 | agree | t_elm_ImportExposingItemsTest |
| ImportOperatorItemTest | sum | 7 | 7 | agree | t_elm_ImportOperatorItemTest |
| ImportOperatorItemTest | quotient | 3 | 3 | agree | t_elm_ImportOperatorItemTest |
| ImportResolutionQualifiedImportedFunctionTest | testValue | [-1,-2] | [-1,-2] | agree | t_elm_ImportResolutionQualifiedImportedFunctionTest |
| ImportTypeByNameLaterReplacesTest | x | 7 | 7 | agree | t_elm_ImportTypeByNameLaterReplacesTest |
| IndirectCallFloatTest | apply_double | 10 | 10 | agree | t_elm_IndirectCallFloatTest |
| IndirectCallFloatTest | apply_negate | -3 | -3 | agree | t_elm_IndirectCallFloatTest |
| IndirectCallFloatTest | apply_addTen | 15 | 15 | agree | t_elm_IndirectCallFloatTest |
| IndirectCallFloatTest | twice_double | 8 | 8 | agree | t_elm_IndirectCallFloatTest |
| IndirectCallFloatTest | twice_addTen | 20 | 20 | agree | t_elm_IndirectCallFloatTest |
| IndirectCallFloatTest | compose_result | 22 | 22 | agree | t_elm_IndirectCallFloatTest |
| InfixAssocLeftArithTest | sub sub | 5 | 5 | agree | t_elm_InfixAssocLeftArithTest |
| InfixAssocLeftArithTest | fdiv fdiv | 5 | 5 | agree | t_elm_InfixAssocLeftArithTest |
| InfixAssocLeftArithTest | idiv idiv | 3 | 3 | agree | t_elm_InfixAssocLeftArithTest |
| InfixAssocPipesTest | pipe right twice | 3 | 3 | agree | t_elm_InfixAssocPipesTest |
| InfixAssocPipesTest | pipe left twice | -3 | -3 | agree | t_elm_InfixAssocPipesTest |
| InfixAssocRightPowTest | pow pow | 512 | 512 | agree | t_elm_InfixAssocRightPowTest (native) |
| InfixIfExtendsRightTest | if then chain | 10 | 10 | agree | t_elm_InfixIfExtendsRightTest |
| InfixLastOperandAnyExprTest | if last | 3 | 3 | agree | t_elm_InfixLastOperandAnyExprTest |
| InfixLastOperandAnyExprTest | lambda last | 10 | 10 | agree | t_elm_InfixLastOperandAnyExprTest |
| InfixNegatedOperandTest | negated pow | 4 | 4 | agree | t_elm_InfixNegatedOperandTest (native) |
| InfixNegatedOperandTest | sub negated | 5 | 5 | agree | t_elm_InfixNegatedOperandTest (native) |
| InfixNonAssocSeparatedLegalTest | separated | True | True | agree | t_elm_InfixNonAssocSeparatedLegalTest |
| InfixPrecAddOverConsTest | add then cons | [2,5] | [2,5] | agree | t_elm_InfixPrecAddOverConsTest |

Elm05: 40 programs, 99 checks, 99 agree.

## Elm06

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| InfixPrecAndOverOrTest | or then and | True | True | agree | t_elm_InfixPrecAndOverOrTest |
| InfixPrecAppendOverEqTest | append then eq | True | True | agree | t_elm_InfixPrecAppendOverEqTest |
| InfixPrecApplicationFirstTest | application then pow | 4 | 4 | agree | t_elm_InfixPrecApplicationFirstTest (native) |
| InfixPrecApplicationFirstTest | application then mul | 9 | 9 | agree | t_elm_InfixPrecApplicationFirstTest (native) |
| InfixPrecCompareOverAndTest | lt then and | True | True | agree | t_elm_InfixPrecCompareOverAndTest |
| InfixPrecComposeOverPipeTest | compose then pipe | -3 | -3 | agree | t_elm_InfixPrecComposeOverPipeTest |
| InfixPrecMulOverAddTest | add then mul | 14 | 14 | agree | t_elm_InfixPrecMulOverAddTest |
| InfixPrecMulOverAddTest | mul then add | 10 | 10 | agree | t_elm_InfixPrecMulOverAddTest |
| InfixPrecOrOverPipeTest | or then pipe | False | False | agree | t_elm_InfixPrecOrOverPipeTest |
| InfixPrecPowOverMulTest | pow then mul | 16 | 16 | agree | t_elm_InfixPrecPowOverMulTest (native) |
| InlineDupLetNamesTest | InlineDupLetNamesTest | 6 | 6 | agree | t_elm_InlineDupLetNamesTest |
| JoinpointABI23Majority3FlatTest | testValue | 10 | 10 | agree | t_elm_JoinpointABI23Majority3FlatTest |
| LambdaBoundaryCaptureTest | result | 105 | 105 | agree | t_elm_LambdaBoundaryCaptureTest |
| LambdaCaseBoundaryTest | add | 7 | 7 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaCaseBoundaryTest | sub | 3 | 3 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaCaseBoundaryTest | mul | 20 | 20 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaCaseBoundaryTest | nested_add | 11 | 11 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaCaseBoundaryTest | nested_sub | 3 | 3 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaCaseBoundaryTest | partial_add | 15 | 15 | agree | t_elm_LambdaCaseBoundaryTest |
| LambdaLetBoundaryTest | basic | 15 | 15 | agree | t_elm_LambdaLetBoundaryTest |
| LambdaLetBoundaryTest | capturing | 19 | 19 | agree | t_elm_LambdaLetBoundaryTest |
| LambdaLetBoundaryTest | multi_let | 20 | 20 | agree | t_elm_LambdaLetBoundaryTest |
| LambdaLetBoundaryTest | nested | 42 | 42 | agree | t_elm_LambdaLetBoundaryTest |
| LambdaLetBoundaryTest | partial | 25 | 25 | agree | t_elm_LambdaLetBoundaryTest |
| LambdaPatternArgTest | swap | (2,1) | (2,1) | agree | t_elm_LambdaPatternArgTest |
| LambdaPatternArgTest | getX | 42 | 42 | agree | t_elm_LambdaPatternArgTest |
| LambdaPatternArgTest | mixed | "b" | "b" | agree | t_elm_LambdaPatternArgTest |
| LargeDispatchCaseTest | r1 | 3 | 3 | agree | t_elm_LargeDispatchCaseTest |
| LargeDispatchCaseTest | r2 | -1 | -1 | agree | t_elm_LargeDispatchCaseTest |
| LargeDispatchCaseTest | r3 | -5 | -5 | agree | t_elm_LargeDispatchCaseTest |
| LargeDispatchCaseTest | r4 | 42 | 42 | agree | t_elm_LargeDispatchCaseTest |
| LetBasicTest | result1 | 5 | 5 | agree | t_elm_LetBasicTest |
| LetBasicTest | result2 | "hello world" | "hello world" | agree | t_elm_LetBasicTest |
| LetBoundLambdaCallTest | result | 1 | 1 | agree | t_elm_LetBoundLambdaCallTest |
| LetDestructAliasTest | pair | (1,2) | (1,2) | agree | t_elm_LetDestructAliasTest |
| LetDestructAliasTest | first | 1 | 1 | agree | t_elm_LetDestructAliasTest |
| LetDestructFuncTupleTest | get | 10 | 10 | agree | t_elm_LetDestructFuncTupleTest |
| LetDestructFuncTupleTest | set | 99 | 99 | agree | t_elm_LetDestructFuncTupleTest |
| LetDestructNestedSingleConstructorNumberTest | testValue | 1.5 | 1.5 | agree | t_elm_LetDestructNestedSingleConstructorNumberTest |
| LetDestructRecordTest | single | 42 | 42 | agree | t_elm_LetDestructRecordTest |
| LetDestructRecordTest | multi | 3 | 3 | agree | t_elm_LetDestructRecordTest |
| LetDestructRecordTest | partial | 4 | 4 | agree | t_elm_LetDestructRecordTest |
| LetDestructRecordTest | mixed | 3 | 3 | agree | t_elm_LetDestructRecordTest |
| LetDestructTupleNestedTest | basic | 3 | 3 | agree | t_elm_LetDestructTupleNestedTest |
| LetDestructTupleNestedTest | nested | 8 | 8 | agree | t_elm_LetDestructTupleNestedTest |
| LetDestructTupleNestedTest | chain | 6 | 6 | agree | t_elm_LetDestructTupleNestedTest |
| LetDestructuringTest | first | 1 | 1 | agree | t_elm_LetDestructuringTest |
| LetDestructuringTest | second | 2 | 2 | agree | t_elm_LetDestructuringTest |
| LetDestructuringTest | head | 10 | 10 | agree | t_elm_LetDestructuringTest |
| LetMultiFuncTest | r1 | 1 | 1 | agree | t_elm_LetMultiFuncTest |
| LetMultiFuncTest | r2 | 2 | 2 | agree | t_elm_LetMultiFuncTest |
| LetMultipleTest | sum | 15 | 15 | agree | t_elm_LetMultipleTest |
| LetMultipleTest | product | 120 | 120 | agree | t_elm_LetMultipleTest |
| LetMutualRecursionBetweenLocalsTest | testValue | 22 | 22 | agree | t_elm_LetMutualRecursionBetweenLocalsTest |
| LetNestedTest | nested | 30 | 30 | agree | t_elm_LetNestedTest |
| LetNumberApplyToTest | applyTo | 45 | 45 | agree | t_elm_LetNumberApplyToTest (native) |
| LetNumberCaseLetTest | caselet | 45 | 45 | agree | t_elm_LetNumberCaseLetTest (native) |
| LetNumberCaseTuple3Test | case-tuple3-int | 60 | 60 | agree | t_elm_LetNumberCaseTuple3Test (native) |
| LetNumberCaseTuple3Test | case-tuple3-float | 61 | 61 | agree | t_elm_LetNumberCaseTuple3Test (native) |
| LetNumberClosureInRecordTest | closrec | 45 | 45 | agree | t_elm_LetNumberClosureInRecordTest (native) |
| LetNumberCustomTriple3Test | tri3 | 180 | 180 | agree | t_elm_LetNumberCustomTriple3Test (native) |
| LetNumberCustomTypeTest | ctor | 45 | 45 | agree | t_elm_LetNumberCustomTypeTest (native) |
| LetNumberDeepNestRecordTest | deeprec | 45 | 45 | agree | t_elm_LetNumberDeepNestRecordTest (native) |
| LetNumberDestructureTest | destructure | 105 | 105 | agree | t_elm_LetNumberDestructureTest (native) |
| LetNumberFloatArithCrashTest | sqrt | 12 | 12 | agree | t_elm_LetNumberFloatArithCrashTest (native) |
| LetNumberFloatArithCrashTest | add | 31 | 31 | agree | t_elm_LetNumberFloatArithCrashTest (native) |
| LetNumberFloatArithCrashTest | div | 6 | 6 | agree | t_elm_LetNumberFloatArithCrashTest (native) |
| LetNumberFloatArithCrashTest | pow | 8 | 8 | agree | t_elm_LetNumberFloatArithCrashTest (native) |
| LetNumberFracRecordTest | frac | 34 | 34 | agree | t_elm_LetNumberFracRecordTest (native) |
| LetNumberIfBranchTest | ifbr | 45 | 45 | agree | t_elm_LetNumberIfBranchTest (native) |
| LetNumberIndirectCaptureTest | capture | 75 | 75 | agree | t_elm_LetNumberIndirectCaptureTest (native) |
| LetNumberIndirectDualTest | dual | (31,45) | (31,45) | agree | t_elm_LetNumberIndirectDualTest (native) |

Elm06: 40 programs, 72 checks, 72 agree.

## Elm07

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| LetNumberIndirectIdentityTest | identity | 45 | 45 | agree | t_elm_LetNumberIndirectIdentityTest (native) |
| LetNumberIndirectTopFnTest | topfn | 45 | 45 | agree | t_elm_LetNumberIndirectTopFnTest (native) |
| LetNumberLetInLambdaTest | lamlet | 45 | 45 | agree | t_elm_LetNumberLetInLambdaTest (native) |
| LetNumberListCaseTest | list-case-int | 2 | 2 | agree | t_elm_LetNumberListCaseTest (native) |
| LetNumberListCaseTest | list-case-float | 3 | 3 | agree | t_elm_LetNumberListCaseTest (native) |
| LetNumberListConsHeadTest | listcons | 45 | 45 | agree | t_elm_LetNumberListConsHeadTest (native) |
| LetNumberListFixedTest | listfixed | 105 | 105 | agree | t_elm_LetNumberListFixedTest (native) |
| LetNumberLogBaseTest | logbase | 2 | 2 | agree | t_elm_LetNumberLogBaseTest (native) |
| LetNumberMaybeCaseDirectTest | maybedirect | 45 | 45 | agree | t_elm_LetNumberMaybeCaseDirectTest (native) |
| LetNumberMixedTupleSlotTest | mixedslot | 105 | 105 | agree | t_elm_LetNumberMixedTupleSlotTest (native) |
| LetNumberMulFnTest | mulFn | 45 | 45 | agree | t_elm_LetNumberMulFnTest (native) |
| LetNumberNegateTest | neg | 12 | 12 | agree | t_elm_LetNumberNegateTest (native) |
| LetNumberNestedCustomTest | nestcustom | 45 | 45 | agree | t_elm_LetNumberNestedCustomTest (native) |
| LetNumberNestedLetTest | nestedlet | 45 | 45 | agree | t_elm_LetNumberNestedLetTest (native) |
| LetNumberNestedTupleTest | nesttup | 155 | 155 | agree | t_elm_LetNumberNestedTupleTest (native) |
| LetNumberRecordDestructureTest | recdestr | 105 | 105 | agree | t_elm_LetNumberRecordDestructureTest (native) |
| LetNumberRecordMultiFieldTest | multi | 105 | 105 | agree | t_elm_LetNumberRecordMultiFieldTest (native) |
| LetNumberRecordToFnTest | rec2fn | 45 | 45 | agree | t_elm_LetNumberRecordToFnTest (native) |
| LetNumberScaleFnTest | scale | 105 | 105 | agree | t_elm_LetNumberScaleFnTest (native) |
| LetNumberTupleRecordNestTest | tuprec | 105 | 105 | agree | t_elm_LetNumberTupleRecordNestTest (native) |
| LetNumberTupleToFnTest | tup2fn | 105 | 105 | agree | t_elm_LetNumberTupleToFnTest (native) |
| LetNumberUnionBranchTest | union | 145 | 145 | agree | t_elm_LetNumberUnionBranchTest (native) |
| LetNumberWildcardSlotTest | wildslot | 120 | 120 | agree | t_elm_LetNumberWildcardSlotTest (native) |
| LetRecClosureTest | LetRecClosureTest | [1,2,3] | [1,2,3] | agree | t_elm_LetRecClosureTest |
| LetRecMultiArgTest | result | 2 | 2 | agree | t_elm_LetRecMultiArgTest |
| LetSeparatedStagingTest | result | 18 | 18 | agree | t_elm_LetSeparatedStagingTest |
| LetValueBindingTest | evaluated | 21 | 21 | agree | t_elm_LetValueBindingTest |
| LetValueBindingTest | doubled | 42 | 42 | agree | t_elm_LetValueBindingTest |
| ListConsCharTest | list | ['a','b','c'] | ['a','b','c'] | agree | t_elm_ListConsCharTest |
| ListConsCharTest | head | Just 'a' | Just 'a' | agree | t_elm_ListConsCharTest |
| ListConsCharTest | prepend | ['z','a','b','c'] | ['z','a','b','c'] | agree | t_elm_ListConsCharTest |
| ListConsFloatTest | list | [1,2.5,3.75] | [1,2.5,3.75] | agree | t_elm_ListConsFloatTest |
| ListConsFloatTest | head | Just 1 | Just 1 | agree | t_elm_ListConsFloatTest |
| ListConsFloatTest | prepend | [0,1,2.5,3.75] | [0,1,2.5,3.75] | agree | t_elm_ListConsFloatTest |
| ListConsIntTest | list | [1,2,3] | [1,2,3] | agree | t_elm_ListConsIntTest |
| ListConsIntTest | head | Just 1 | Just 1 | agree | t_elm_ListConsIntTest |
| ListConsIntTest | prepend | [0,1,2,3] | [0,1,2,3] | agree | t_elm_ListConsIntTest |
| ListConsTest | cons1 | [1] | [1] | agree | t_elm_ListConsTest |
| ListConsTest | cons2 | [1,2] | [1,2] | agree | t_elm_ListConsTest |
| ListConsTest | cons3 | [1,2,3] | [1,2,3] | agree | t_elm_ListConsTest |
| ListIndexedMapTest | testValue | [] | [] | agree | t_elm_ListIndexedMapTest |
| ListLiteralTest | list1 | [1] | [1] | agree | t_elm_ListLiteralTest |
| ListLiteralTest | list2 | [1,2,3] | [1,2,3] | agree | t_elm_ListLiteralTest |
| ListLiteralTest | list3 | [10,20,30,40,50] | [10,20,30,40,50] | agree | t_elm_ListLiteralTest |
| LocalMultiNonTailRecTest | sumInt | 6 | 6 | agree | t_elm_LocalMultiNonTailRecTest |
| LocalMultiNonTailRecTest | sumFloat | 4 | 4 | agree | t_elm_LocalMultiNonTailRecTest |
| LocalRecCaptureBoolTest | count_true | 3 | 3 | agree | t_elm_LocalRecCaptureBoolTest |
| LocalRecCaptureBoolTest | count_false | 4 | 4 | agree | t_elm_LocalRecCaptureBoolTest |
| LocalRecCaptureKindsTest | direct | 110 | 110 | agree | t_elm_LocalRecCaptureKindsTest (native) |
| LocalRecCaptureKindsTest | via_hof | [110,110] | [110,110] | agree | t_elm_LocalRecCaptureKindsTest (native) |
| LocalRecCaptureSplitParamTest | o2 | 9 | 9 | agree | t_elm_LocalRecCaptureSplitParamTest |
| LocalRecCaptureSplitParamTest | o3 | 9 | 9 | agree | t_elm_LocalRecCaptureSplitParamTest |
| LocalTailRecSimpleTest | result | 55 | 55 | agree | t_elm_LocalTailRecSimpleTest |
| LssGapBodyTieAnnoAB | bodyTieAnn | 7 | 7 | agree | t_elm_LssGapBodyTieAnnoAB |
| LssGapBodyTieAnnoAB | bodyTieInf | 7 | 7 | agree | t_elm_LssGapBodyTieAnnoAB |
| LssGapCtorAsValue | ctorAsValue | 7 | 7 | agree | t_elm_LssGapCtorAsValue |
| LssGapCtorInList | ctorInList | 7 | 7 | agree | t_elm_LssGapCtorInList |

Elm07: 40 programs, 57 checks, 57 agree.

## Elm08

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| LssGapCtorScale | ctorScale | 10 | 10 | agree | t_elm_LssGapCtorScale |
| LssGapCustomTypeFn | customTypeFn | 14 | 14 | agree | t_elm_LssGapCustomTypeFn |
| LssGapNoDecls | noDecls | 14 | 14 | agree | t_elm_LssGapNoDecls |
| LssGapRecordFnNoAlias | recordFnNoAlias | 14 | 14 | agree | t_elm_LssGapRecordFnNoAlias |
| LssGapTupleFn | tupleFn | 14 | 14 | agree | t_elm_LssGapTupleFn |
| MaybeJustTest | just1 | Just 42 | Just 42 | agree | t_elm_MaybeJustTest |
| MaybeJustTest | just2 | Just "hello" | Just "hello" | agree | t_elm_MaybeJustTest |
| MaybeJustTest | just3 | Just True | Just True | agree | t_elm_MaybeJustTest |
| MaybeNothingTest | nothing | Nothing | Nothing | agree | t_elm_MaybeNothingTest |
| MaybePatternMatchTest | match1 | 42 | 42 | agree | t_elm_MaybePatternMatchTest |
| MaybePatternMatchTest | match2 | 0 | 0 | agree | t_elm_MaybePatternMatchTest |
| MultiLocalTailRecTest | result | 15 | 15 | agree | t_elm_MultiLocalTailRecTest |
| MutualLetRecClosuresTest | evenResult | True | True | agree | t_elm_MutualLetRecClosuresTest |
| MutualLetRecClosuresTest | oddResult | False | False | agree | t_elm_MutualLetRecClosuresTest |
| MutualLetRecClosuresTest | callsEven | 4 | 4 | agree | t_elm_MutualLetRecClosuresTest |
| MutualLetRecClosuresTest | callsOdd | 3 | 3 | agree | t_elm_MutualLetRecClosuresTest |
| MutualLetRecManyCapturesTest | go 3 | 42 | 42 | agree | t_elm_MutualLetRecManyCapturesTest |
| MutualLetRecManyCapturesTest | go 2 | 42 | 42 | agree | t_elm_MutualLetRecManyCapturesTest |
| MutualLetRecManyCapturesTest | go 1 | 42 | 42 | agree | t_elm_MutualLetRecManyCapturesTest |
| MutualLetRecManyCapturesTest | go 0 | 42 | 42 | agree | t_elm_MutualLetRecManyCapturesTest |
| MutualLetRecNestedTest | run 3 | 42 | 42 | agree | t_elm_MutualLetRecNestedTest |
| MutualLetRecNestedTest | run 2 | 84 | 84 | agree | t_elm_MutualLetRecNestedTest |
| MutualLetRecNestedTest | run 1 | 42 | 42 | agree | t_elm_MutualLetRecNestedTest |
| MutualLetRecNestedTest | run 0 | 84 | 84 | agree | t_elm_MutualLetRecNestedTest |
| MutualRecursionTest | isEven0 | True | True | agree | t_elm_MutualRecursionTest |
| MutualRecursionTest | isEven5 | False | False | agree | t_elm_MutualRecursionTest |
| MutualRecursionTest | isOdd5 | True | True | agree | t_elm_MutualRecursionTest |
| MutualRecursionThreeWayTest | a10 | 1 | 1 | agree | t_elm_MutualRecursionThreeWayTest |
| MutualRecursionThreeWayTest | a9 | 0 | 0 | agree | t_elm_MutualRecursionThreeWayTest |
| MutualRecursionThreeWayTest | a3 | 0 | 0 | agree | t_elm_MutualRecursionThreeWayTest |
| MutualRecursionThreeWayTest | a0 | 0 | 0 | agree | t_elm_MutualRecursionThreeWayTest |
| NestedCaseReturnTest | r1 | "integer" | "integer" | agree | t_elm_NestedCaseReturnTest |
| NestedCaseReturnTest | r2 | "text" | "text" | agree | t_elm_NestedCaseReturnTest |
| NestedCaseReturnTest | r3 | "custom List" | "custom List" | agree | t_elm_NestedCaseReturnTest |
| NestedCaseReturnTest | r4 | "other" | "other" | agree | t_elm_NestedCaseReturnTest |
| NestedCaseReturnTest | r5 | "empty" | "empty" | agree | t_elm_NestedCaseReturnTest |
| NonAsciiIdentifierTest | NonAsciiIdentifierTest | 7 | 7 | agree | t_elm_NonAsciiIdentifierTest |
| NonZeroArityRecursionTest | countDown | 0 | 0 | agree | t_elm_NonZeroArityRecursionTest |
| NumberDestructFieldTest | tuple field | 2.5 | 2.5 | agree | t_elm_NumberDestructFieldTest |
| NumberDestructFieldTest | list field | 1.25 | 1.25 | agree | t_elm_NumberDestructFieldTest |
| NumberDestructFieldTest | record field | 4.5 | 4.5 | agree | t_elm_NumberDestructFieldTest |
| NumberDestructFieldTest | maybe field | 5.5 | 5.5 | agree | t_elm_NumberDestructFieldTest |
| NumberDestructFieldTest | nested | (3.5,4) | (3.5,4) | agree | t_elm_NumberDestructFieldTest |
| NumberGenericAppCustom | numgenapp | 45 | 45 | agree | t_elm_NumberGenericAppCustom (native) |
| PapEtaCtorProbe | final | { depth = 9, stats = { a = 2, b = 2, shape = 4 } } | { depth = 9, stats = { a = 2, b = 2, shape = 4 } } | agree | t_elm_PapEtaCtorProbe |
| ParenthesesTest | grouped | 9 | 9 | agree | t_elm_ParenthesesTest |
| ParenthesesTest | ungrouped | 7 | 7 | agree | t_elm_ParenthesesTest |
| ParenthesesTest | redundant | 5 | 5 | agree | t_elm_ParenthesesTest |
| ParenthesesTest | nested pattern | [3,0,-1] | [3,0,-1] | agree | t_elm_ParenthesesTest |
| ParenthesesTest | parenthesised types | [2,4] | [2,4] | agree | t_elm_ParenthesesTest |
| PartialAppCaptureTypesTest | float_cap | 1.5 | 1.5 | agree | t_elm_PartialAppCaptureTypesTest |
| PartialAppCaptureTypesTest | char_cap | 'x' | 'x' | agree | t_elm_PartialAppCaptureTypesTest |
| PartialAppCaptureTypesTest | bool_cap | True | True | agree | t_elm_PartialAppCaptureTypesTest |
| PartialAppCaptureTypesTest | string_cap | "hello" | "hello" | agree | t_elm_PartialAppCaptureTypesTest |
| PartialAppCaptureTypesTest | combined | 3.5 | 3.5 | agree | t_elm_PartialAppCaptureTypesTest |
| PartialAppChainTest | chain1 | 10 | 10 | agree | t_elm_PartialAppChainTest |
| PartialAppChainTest | chain2 | 6 | 6 | agree | t_elm_PartialAppChainTest |
| PartialApplicationTest | partial1 | 7 | 7 | agree | t_elm_PartialApplicationTest |
| PartialApplicationTest | partial2 | 15 | 15 | agree | t_elm_PartialApplicationTest |
| PartialApplicationTest | partial3 | [2,3,4] | [2,3,4] | agree | t_elm_PartialApplicationTest |
| PhantomTypeVarTest | result | 42 | 42 | agree | t_elm_PhantomTypeVarTest |
| PolyApplyLambdaTest | applyIntId | 1 | 1 | agree | t_elm_PolyApplyLambdaTest |
| PolyApplyLambdaTest | applyStrId | "hi" | "hi" | agree | t_elm_PolyApplyLambdaTest |
| PolyApplyLambdaTest | applyLambda | 42 | 42 | agree | t_elm_PolyApplyLambdaTest |
| PolyChainCallTest | size | 2 | 2 | agree | t_elm_PolyChainCallTest |
| PolyChainDictLikeInsertChained5TimesWithTupleKeysConcreteCallerTest | testValue | 1 | 1 | agree | t_elm_PolyChainDictLikeInsertChained5TimesWithTupleKeysConcreteCallerTest |
| PolyChainFoldlLikeCalled8TimesOverTupleKeyedStructureTest | testValue | 0 | 0 | agree | t_elm_PolyChainFoldlLikeCalled8TimesOverTupleKeyedStructureTest |
| PolyEscapePolymorphicFunctionExtractedFromTupleTest | testValue | 42 | 42 | agree | t_elm_PolyEscapePolymorphicFunctionExtractedFromTupleTest |
| PolyEscapeRecordTest | result | 42 | 42 | agree | t_elm_PolyEscapeRecordTest |
| PolyEscapeRecordTest | narrowed | 6 | 6 | agree | t_elm_PolyEscapeRecordTest |
| PolyLetConstTest | r1 | 1 | 1 | agree | t_elm_PolyLetConstTest |
| PolyLetConstTest | r2 | "hi" | "hi" | agree | t_elm_PolyLetConstTest |
| PolyLetTailRecTwoTypesTest | r | (6,2) | (6,2) | agree | t_elm_PolyLetTailRecTwoTypesTest |
| PolySpecializeRecursiveTest | intLen | 3 | 3 | agree | t_elm_PolySpecializeRecursiveTest |
| PolySpecializeRecursiveTest | strLen | 2 | 2 | agree | t_elm_PolySpecializeRecursiveTest |
| PolySpecializeRecursiveTest | intMap | [2,4,6] | [2,4,6] | agree | t_elm_PolySpecializeRecursiveTest |
| PolySpecializeRecursiveTest | strMap | ["aa","bb"] | ["aa","bb"] | agree | t_elm_PolySpecializeRecursiveTest |
| PolyStepLoopFloatResultTest | result | 3.14 | 3.14 | agree | t_elm_PolyStepLoopFloatResultTest |
| PolyStepLoopFloatResultTest | state | 6 | 6 | agree | t_elm_PolyStepLoopFloatResultTest |
| PolyStepLoopFoldMIntTest | sum | 15 | 15 | agree | t_elm_PolyStepLoopFoldMIntTest |
| PolyStepLoopFoldMIntTest | final | 104 | 104 | agree | t_elm_PolyStepLoopFoldMIntTest |
| PolyTailRecReverseTest | intRev | [3,2,1] | [3,2,1] | agree | t_elm_PolyTailRecReverseTest |
| PolyTailRecReverseTest | strRev | ["c","b","a"] | ["c","b","a"] | agree | t_elm_PolyTailRecReverseTest |
| PortEncodingDecodeFloatTest | testValue | 0 | 0 | agree | t_elm_PortEncodingDecodeFloatTest |
| PortEncodingDecodeListIntTest | testValue | 0 | 0 | agree | t_elm_PortEncodingDecodeListIntTest |
| PortEncodingDecodeMaybeIntTest | testValue | 0 | 0 | agree | t_elm_PortEncodingDecodeMaybeIntTest |

Elm08: 40 programs, 86 checks, 86 agree.

## Elm09

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| PortEncodingDecodeTuple2Test | testValue | 0 | 0 | agree | t_elm_PortEncodingDecodeTuple2Test |
| PortEncodingEncodeBoolTest | testValue | 0 | 0 | agree | t_elm_PortEncodingEncodeBoolTest |
| PortEncodingEncodeFloatTest | testValue | 0 | 0 | agree | t_elm_PortEncodingEncodeFloatTest |
| PortEncodingEncodeMaybeRecordTest | testValue | 0 | 0 | agree | t_elm_PortEncodingEncodeMaybeRecordTest |
| PortEncodingEncodeTuple2Test | testValue | 0 | 0 | agree | t_elm_PortEncodingEncodeTuple2Test |
| PortEncodingPortWithArrayTest | testValue | 0 | 0 | agree | t_elm_PortEncodingPortWithArrayTest |
| PureMutualRecursiveValueTest | ok | () | () | agree | t_elm_PureMutualRecursiveValueTest |
| PureRecursiveValueThunkTest | ok | () | () | agree | t_elm_PureRecursiveValueThunkTest |
| RecordAccessTest | x | 1 | 1 | agree | t_elm_RecordAccessTest |
| RecordAccessTest | y | 2 | 2 | agree | t_elm_RecordAccessTest |
| RecordAccessTest | name | "Alice" | "Alice" | agree | t_elm_RecordAccessTest |
| RecordAccessorFunctionCaseTest | testValue | 1 | 1 | agree | t_elm_RecordAccessorFunctionCaseTest |
| RecordAccessorFunctionTest | names | ["Alice","Bob"] | ["Alice","Bob"] | agree | t_elm_RecordAccessorFunctionTest |
| RecordAccessorFunctionTest | xs | [1,4] | [1,4] | agree | t_elm_RecordAccessorFunctionTest |
| RecordChainedUpdateTest | multi | { x = 100, y = 20, z = 300 } | { x = 100, y = 20, z = 300 } | agree | t_elm_RecordChainedUpdateTest |
| RecordChainedUpdateTest | chain | { x = 10, y = 20 } | { x = 10, y = 20 } | agree | t_elm_RecordChainedUpdateTest |
| RecordChainedUpdatesTest | testValue | { x = 10, y = 20 } | { x = 10, y = 20 } | agree | t_elm_RecordChainedUpdatesTest |
| RecordCreateTest | record1 | { x = 1, y = 2 } | { x = 1, y = 2 } | agree | t_elm_RecordCreateTest |
| RecordCreateTest | record2 | { age = 30, name = "Alice" } | { age = 30, name = "Alice" } | agree | t_elm_RecordCreateTest |
| RecordNestedAccessTest | deep | 42 | 42 | agree | t_elm_RecordNestedAccessTest |
| RecordNestedAccessTest | chain | 99 | 99 | agree | t_elm_RecordNestedAccessTest |
| RecordRowsTest | sum of fields | 3 | 3 | agree | t_elm_RecordRowsTest |
| RecordRowsTest | label | "p" | "p" | agree | t_elm_RecordRowsTest |
| RecordRowsTest | constructor order | (1,2) | (1,2) | agree | t_elm_RecordRowsTest |
| RecordRowsTest | unit | 5 | 5 | agree | t_elm_RecordRowsTest |
| RecordUpdatePolyFieldTest | f | 6 | 6 | agree | t_elm_RecordUpdatePolyFieldTest |
| RecordUpdatePolyFieldTest | g | 0 | 0 | agree | t_elm_RecordUpdatePolyFieldTest |
| RecordUpdateTest | updated | { x = 10, y = 2 } | { x = 10, y = 2 } | agree | t_elm_RecordUpdateTest |
| RecordUpdateTest | original | { x = 1, y = 2 } | { x = 1, y = 2 } | agree | t_elm_RecordUpdateTest |
| RecordWithFunctionsTest | apply1 | 11 | 11 | agree | t_elm_RecordWithFunctionsTest |
| RecordWithFunctionsTest | apply2 | 20 | 20 | agree | t_elm_RecordWithFunctionsTest |
| RecordWithFunctionsTest | composed | 22 | 22 | agree | t_elm_RecordWithFunctionsTest |
| RecordWithFunctionsTest | updated | 7 | 7 | agree | t_elm_RecordWithFunctionsTest |
| RecursiveFactorialTest | fact0 | 1 | 1 | agree | t_elm_RecursiveFactorialTest |
| RecursiveFactorialTest | fact5 | 120 | 120 | agree | t_elm_RecursiveFactorialTest |
| RecursiveFactorialTest | fact10 | 3628800 | 3628800 | agree | t_elm_RecursiveFactorialTest |
| RecursiveFibonacciTest | fib0 | 0 | 0 | agree | t_elm_RecursiveFibonacciTest |
| RecursiveFibonacciTest | fib1 | 1 | 1 | agree | t_elm_RecursiveFibonacciTest |
| RecursiveFibonacciTest | fib10 | 55 | 55 | agree | t_elm_RecursiveFibonacciTest |
| RecursiveListLengthTest | len0 | 0 | 0 | agree | t_elm_RecursiveListLengthTest |
| RecursiveListLengthTest | len3 | 3 | 3 | agree | t_elm_RecursiveListLengthTest |
| RecursiveListLengthTest | len5 | 5 | 5 | agree | t_elm_RecursiveListLengthTest |
| RecursiveMutualTypeTest | nodes | 4 | 4 | agree | t_elm_RecursiveMutualTypeTest |
| RecursiveTopLevelLambdaTest | testValue | 4 | 4 | agree | t_elm_RecursiveTopLevelLambdaTest |
| RecursiveTreeTest | sum | 6 | 6 | agree | t_elm_RecursiveTreeTest |
| RecursiveTreeTest | depth | 3 | 3 | agree | t_elm_RecursiveTreeTest |
| RecursiveTypeInRecordTest | eval | 6 | 6 | agree | t_elm_RecursiveTypeInRecordTest |
| ResultErrTest | err1 | Err "failed" | Err "failed" | agree | t_elm_ResultErrTest |
| ResultErrTest | err2 | Err 404 | Err 404 | agree | t_elm_ResultErrTest |
| ResultOkTest | ok1 | Ok 42 | Ok 42 | agree | t_elm_ResultOkTest |
| ResultOkTest | ok2 | Ok "success" | Ok "success" | agree | t_elm_ResultOkTest |
| RowVariableAloneTest | x | 1 | 1 | agree | t_elm_RowVariableAloneTest |
| RowVariableAloneTest | rest z | "b" | "b" | agree | t_elm_RowVariableAloneTest |
| SingleCtorPairBoolCharTest | match_true | "yes" | "yes" | agree | t_elm_SingleCtorPairBoolCharTest |
| SingleCtorPairBoolCharTest | match_false | "no" | "no" | agree | t_elm_SingleCtorPairBoolCharTest |
| SingleCtorPairBoolCharTest | unwrap_char | 'x' | 'x' | agree | t_elm_SingleCtorPairBoolCharTest |
| SingleCtorPairBoolFloatTest | match_true | "yes" | "yes" | agree | t_elm_SingleCtorPairBoolFloatTest |
| SingleCtorPairBoolFloatTest | match_false | "no" | "no" | agree | t_elm_SingleCtorPairBoolFloatTest |
| SingleCtorPairBoolFloatTest | unwrap_float | 3.14 | 3.14 | agree | t_elm_SingleCtorPairBoolFloatTest |
| SingleCtorPairBoolIntBidiTest | match_true | "yes" | "yes" | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairBoolIntBidiTest | match_false | "no" | "no" | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairBoolIntBidiTest | match_pos | "positive" | "positive" | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairBoolIntBidiTest | match_neg | "non-positive" | "non-positive" | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairBoolIntBidiTest | extract_bool | True | True | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairBoolIntBidiTest | extract_int | 42 | 42 | agree | t_elm_SingleCtorPairBoolIntBidiTest |
| SingleCtorPairCharFloatTest | unwrap_char | 'Z' | 'Z' | agree | t_elm_SingleCtorPairCharFloatTest |
| SingleCtorPairCharFloatTest | unwrap_float | 1.5 | 1.5 | agree | t_elm_SingleCtorPairCharFloatTest |
| SingleCtorPairCharFloatTest | match_char | ("got",'Z') | ("got",'Z') | agree | t_elm_SingleCtorPairCharFloatTest |
| SingleCtorPairCharIntTest | unwrap_char | 'A' | 'A' | agree | t_elm_SingleCtorPairCharIntTest |
| SingleCtorPairCharIntTest | unwrap_int | 256 | 256 | agree | t_elm_SingleCtorPairCharIntTest |
| SingleCtorPairCharIntTest | match_char | ("got",'A') | ("got",'A') | agree | t_elm_SingleCtorPairCharIntTest |
| SingleCtorPairFloatBoolTest | unwrap_float | 9.81 | 9.81 | agree | t_elm_SingleCtorPairFloatBoolTest |
| SingleCtorPairFloatBoolTest | match_true | "yes" | "yes" | agree | t_elm_SingleCtorPairFloatBoolTest |
| SingleCtorPairFloatBoolTest | match_false | "no" | "no" | agree | t_elm_SingleCtorPairFloatBoolTest |
| SingleCtorPairFloatBoolTest | match_float | "big" | "big" | agree | t_elm_SingleCtorPairFloatBoolTest |
| SingleCtorPairIntFloatTest | unwrap_int | 42 | 42 | agree | t_elm_SingleCtorPairIntFloatTest |
| SingleCtorPairIntFloatTest | unwrap_float | 2.718 | 2.718 | agree | t_elm_SingleCtorPairIntFloatTest |
| SingleCtorPairIntFloatTest | match_int_pos | "positive" | "positive" | agree | t_elm_SingleCtorPairIntFloatTest |
| SingleCtorPairIntFloatTest | match_float_big | "big" | "big" | agree | t_elm_SingleCtorPairIntFloatTest |
| SingleCtorPairStringBoolTest | unwrap_str | "world" | "world" | agree | t_elm_SingleCtorPairStringBoolTest |
| SingleCtorPairStringBoolTest | match_true | "yes" | "yes" | agree | t_elm_SingleCtorPairStringBoolTest |
| SingleCtorPairStringBoolTest | match_false | "no" | "no" | agree | t_elm_SingleCtorPairStringBoolTest |
| SingleCtorPairStringIntTest | unwrap_str | "hello" | "hello" | agree | t_elm_SingleCtorPairStringIntTest |
| SingleCtorPairStringIntTest | unwrap_int | 99 | 99 | agree | t_elm_SingleCtorPairStringIntTest |
| SingleCtorPairStringIntTest | match_str | "found_hello" | "found_hello" | agree | t_elm_SingleCtorPairStringIntTest |
| SingleCtorPairUnitIntTest | unwrap_unit | () | () | agree | t_elm_SingleCtorPairUnitIntTest |
| SingleCtorPairUnitIntTest | unwrap_int | 77 | 77 | agree | t_elm_SingleCtorPairUnitIntTest |
| SingleCtorPairUnitIntTest | match_unit | "got_unit" | "got_unit" | agree | t_elm_SingleCtorPairUnitIntTest |
| StandardA56PrefixAndOrTest | second argument of (&&) | True | True | agree | t_elm_StandardA56PrefixAndOrTest |
| StandardA56PrefixAndOrTest | (&&) False _ | False | False | agree | t_elm_StandardA56PrefixAndOrTest |
| StandardA56PrefixAndOrTest | second argument of (\|\|) | False | False | agree | t_elm_StandardA56PrefixAndOrTest |
| StandardA56PrefixAndOrTest | (\|\|) True _ | True | True | agree | t_elm_StandardA56PrefixAndOrTest |

Elm09: 40 programs, 92 checks, 92 agree.

## Elm10

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| StandardA82MainInImportedModuleTest | helper main + 1 | 43 | 43 | agree | t_elm_StandardA82MainInImportedModuleTest |
| StandardA93MutualNumberDefaultTest | f 3 | 1 | 1 | agree | t_elm_StandardA93MutualNumberDefaultTest (native) |
| StandardA97NeverErrBranchTest | value (Ok 3) | 3 | 3 | agree | t_elm_StandardA97NeverErrBranchTest |
| StandardA97SelfOnlyTypeTest | fromResult (Ok 3) | 3 | 3 | agree | t_elm_StandardA97SelfOnlyTypeTest |
| StandardApplicationStrictTest | before | () | () | agree (partial log) |  |
| StandardApplicationStrictTest | app strict | (no value) | (no meaning) | agree | t_elm_StandardApplicationStrictTest |
| StandardCoreEvaluationExamplesTest | as-pattern | (1,[1,2]) | (1,[1,2]) | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | unit pattern | 5 | 5 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | operator value | 3 | 3 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | partial basic value | <function> | <function> | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | partial constructor | <function> | <function> | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | (&&) is strict | False | False | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | pipe | 6 | 6 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | mrule-fail | 2 | 2 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | Just 1 | Just 1 | Just 1 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | inc 0.5 | 1.5 | 1.5 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | modBy 4 -5 | 3 | 3 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | remainderBy 4 -5 | -1 | -1 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | record field order | True | True | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | compare strings | LT | LT | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardCoreEvaluationExamplesTest | accessor | 7 | 7 | agree | t_elm_StandardCoreEvaluationExamplesTest |
| StandardLetStrictTest | before | () | () | agree (partial log) |  |
| StandardLetStrictTest | let strict | (no value) | (no meaning) | agree | t_elm_StandardLetStrictTest |
| StringCasePatternCommaTest | one_comma | "comma" | "comma" | agree | t_elm_StringCasePatternCommaTest |
| StringCasePatternCommaTest | one_a | "other" | "other" | agree | t_elm_StringCasePatternCommaTest |
| StringCasePatternCommaTest | two_a | "a" | "a" | agree | t_elm_StringCasePatternCommaTest |
| StringCasePatternCommaTest | two_b | "b" | "b" | agree | t_elm_StringCasePatternCommaTest |
| StringCasePatternCommaTest | two_comma | "other" | "other" | agree | t_elm_StringCasePatternCommaTest |
| StringCreationMatrixTest | Creation.eq | True | True | agree | t_elm_StringCreationMatrixTest |
| StringCreationMatrixTest | Creation.case | True | True | agree | t_elm_StringCreationMatrixTest |
| StringEscapeCrTest | cr | True | True | agree | t_elm_StringEscapeCrTest |
| StringEscapeCrTest | mixed | True | True | agree | t_elm_StringEscapeCrTest |
| StringEscapeCrTest | crlf | True | True | agree | t_elm_StringEscapeCrTest |
| StringEscapeCrTest | triple | True | True | agree | t_elm_StringEscapeCrTest |
| StringEscapeCrTest | pattern | "carriage return" | "carriage return" | agree | t_elm_StringEscapeCrTest |
| StringEscapesTest | newline |  | "line1\nline2" | agree | t_elm_StringEscapesTest |
| StringEscapesTest | tab |  | "col1\tcol2" | agree | t_elm_StringEscapesTest |
| StringEscapesTest | quote | "\"" | "\"" | agree | t_elm_StringEscapesTest |
| StringLiteralTest | str1 | "Hello" | "Hello" | agree | t_elm_StringLiteralTest |
| StringLiteralTest | str2 | "Hello, World!" | "Hello, World!" | agree | t_elm_StringLiteralTest |
| StringLiteralTest | str3 | "abc123" | "abc123" | agree | t_elm_StringLiteralTest |
| StringMagicPrefixTest | s1 | "__mlir_unknown_loc__" | "__mlir_unknown_loc__" | agree | t_elm_StringMagicPrefixTest |
| StringMagicPrefixTest | s2 | "__mlir_loc__:foo:1:2" | "__mlir_loc__:foo:1:2" | agree | t_elm_StringMagicPrefixTest |
| StringMagicPrefixTest | s3 | "__mlir_loc__:" | "__mlir_loc__:" | agree | t_elm_StringMagicPrefixTest |
| StringMagicPrefixTest | s4 | "loc:unknown" | "loc:unknown" | agree | t_elm_StringMagicPrefixTest |
| TailLoopMutualRecMutualRecursionInsideATailLoopTest | testValue | 2 | 2 | agree | t_elm_TailLoopMutualRecMutualRecursionInsideATailLoopTest |
| TailRecBoolCarryTest | result1 | 10 | 10 | agree | t_elm_TailRecBoolCarryTest |
| TailRecBoolCarryTest | result2 | 0 | 0 | agree | t_elm_TailRecBoolCarryTest |
| TailRecBoolCarryTest | result3 | 42 | 42 | agree | t_elm_TailRecBoolCarryTest |
| TailRecCaseDestructTest | foldl | 15 | 15 | agree | t_elm_TailRecCaseDestructTest |
| TailRecCaseDestructTest | sum | 10 | 10 | agree | t_elm_TailRecCaseDestructTest |
| TailRecCaseDestructTest | count | 3 | 3 | agree | t_elm_TailRecCaseDestructTest |
| TailRecCaseMultiBranchTypesTest | result | FoundLE 2 | FoundLE 2 | agree | t_elm_TailRecCaseMultiBranchTypesTest |
| TailRecClosureAccTest | result | 15 | 15 | agree | t_elm_TailRecClosureAccTest |
| TailRecCustomCaseTest | total | 10 | 10 | agree | t_elm_TailRecCustomCaseTest |
| TailRecDeciderSearchTest | found | 42 | 42 | agree | t_elm_TailRecDeciderSearchTest |
| TailRecDecoderLoopTest | r1 | "decode_int" | "decode_int" | agree | t_elm_TailRecDecoderLoopTest |
| TailRecDecoderLoopTest | r2 | "decode_string" | "decode_string" | agree | t_elm_TailRecDecoderLoopTest |
| TailRecDecoderLoopTest | r3 | "decode_list(decode_int)" | "decode_list(decode_int)" | agree | t_elm_TailRecDecoderLoopTest |
| TailRecDecoderLoopTest | r4 | "decode_custom(Foo)" | "decode_custom(Foo)" | agree | t_elm_TailRecDecoderLoopTest |
| TailRecFoldlCaseTest | result | 6 | 6 | agree | t_elm_TailRecFoldlCaseTest |
| TailRecManyBranchStringTest | result | "found-beta" | "found-beta" | agree | t_elm_TailRecManyBranchStringTest |
| TailRecMultiCaseWhileTest | total | 8 | 8 | agree | t_elm_TailRecMultiCaseWhileTest |
| TailRecMultiCaseWhileTest | special | 2 | 2 | agree | t_elm_TailRecMultiCaseWhileTest |
| TailRecNestedCaseTest | find | True | True | agree | t_elm_TailRecNestedCaseTest |
| TailRecNestedCaseTest | nofind | False | False | agree | t_elm_TailRecNestedCaseTest |
| TailRecNestedCaseTest | last | 4 | 4 | agree | t_elm_TailRecNestedCaseTest |
| TailRecNestedStringCaseTest | result | 42 | 42 | agree | t_elm_TailRecNestedStringCaseTest |
| TailRecTypeTraversalTest | result | "integer" | "integer" | agree | t_elm_TailRecTypeTraversalTest |
| TailRecursiveSumTest | sum1 | 15 | 15 | agree | t_elm_TailRecursiveSumTest |
| TailRecursiveSumTest | sum2 | 55 | 55 | agree | t_elm_TailRecursiveSumTest |
| TailRecursiveSumTest | sum3 | 5050 | 5050 | agree | t_elm_TailRecursiveSumTest |
| TopLevelNameReplacesImportTest | own max | 3 | 3 | agree | t_elm_TopLevelNameReplacesImportTest |
| TopLevelNameReplacesImportTest | Basics.max | 2 | 2 | agree | t_elm_TopLevelNameReplacesImportTest |
| TupleCharFieldTest | pair | ('A',65) | ('A',65) | agree | t_elm_TupleCharFieldTest |
| TuplePairTest | pair1 | (1,2) | (1,2) | agree | t_elm_TuplePairTest |
| TuplePairTest | pair2 | ("a","b") | ("a","b") | agree | t_elm_TuplePairTest |
| TuplePairTest | pair3 | (True,False) | (True,False) | agree | t_elm_TuplePairTest |
| TupleTripleTest | triple1 | (1,2,3) | (1,2,3) | agree | t_elm_TupleTripleTest |
| TupleTripleTest | triple2 | ("a","b","c") | ("a","b","c") | agree | t_elm_TupleTripleTest |
| TypeAliasCtorTest | result | { bold = True, count = 42 } | { bold = True, count = 42 } | agree | t_elm_TypeAliasCtorTest |
| TypeClassConstraintTest | absInt | 5 | 5 | agree | t_elm_TypeClassConstraintTest |
| TypeClassConstraintTest | absFloat | 3.14 | 3.14 | agree | t_elm_TypeClassConstraintTest |
| TypeClassConstraintTest | minInt | 3 | 3 | agree | t_elm_TypeClassConstraintTest |
| TypeClassConstraintTest | concatStr | "hello world" | "hello world" | agree | t_elm_TypeClassConstraintTest |
| UnreachableModuleTest | ran | True | True | agree | t_elm_UnreachableModuleTest |
| UserBoolNamedCtorTest | pickTrue | 1 | 1 | agree | t_elm_UserBoolNamedCtorTest |
| UserBoolNamedCtorTest | pickFalse | 2 | 2 | agree | t_elm_UserBoolNamedCtorTest |
| UserBoolNamedCtorTest | pickUnknown | 3 | 3 | agree | t_elm_UserBoolNamedCtorTest |
| UserBoolNamedCtorTest | names | ["T","F","U"] | ["T","F","U"] | agree | t_elm_UserBoolNamedCtorTest |
| WideClosureSat26Test | res | [6208,6215] | [6208,6215] | agree | t_elm_WideClosureSat26Test |
| WideCtorField24Test | field23 | 1023 | 1023 | agree | t_elm_WideCtorField24Test |
| WideCtorField24Test | field24 | 1024 | 1024 | agree | t_elm_WideCtorField24Test |
| WideCtorField24Test | field25 | 2.5 | 2.5 | agree | t_elm_WideCtorField24Test |
| WideCtorField24Test | field26 | 'z' | 'z' | agree | t_elm_WideCtorField24Test |
| WideCtorField24Test | sum24 | 2048 | 2048 | agree | t_elm_WideCtorField24Test |
| WideCtorMixedTest | field23 | "23s" | "23s" | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | field24 | True | True | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | field55 | 1055 | 1055 | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | field59 | False | False | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | eq self | True | True | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | eq other | False | False | agree | t_elm_WideCtorMixedTest |
| WideCtorMixedTest | show | W 1000 1.5 'c' "3s" True 1005 6.5 'h' "8s" False 1010 11.5 'm' "13s" True 1015 16.5 'r' "18s" False 1020 21.5 'w' "23s" True 1025 26.5 'b' "28s" False 1030 31.5 'g' "33s" True 1035 36.5 'l' "38s" False 1040 41.5 'q' "43s" True 1045 46.5 'v' "48s" False 1050 51.5 'a' "53s" True 1055 56.5 'f' "58s" False | W 1000 1.5 'c' "3s" True 1005 6.5 'h' "8s" False 1010 11.5 'm' "13s" True 1015 16.5 'r' "18s" False 1020 21.5 'w' "23s" True 1025 26.5 'b' "28s" False 1030 31.5 'g' "33s" True 1035 36.5 'l' "38s" False 1040 41.5 'q' "43s" True 1045 46.5 'v' "48s" False 1050 51.5 'a' "53s" True 1055 56.5 'f' "58s" False | agree | t_elm_WideCtorMixedTest |
| WideRecord33Test | f0000 | 1000 | 1000 | agree | t_elm_WideRecord33Test |
| WideRecord33Test | f0031 | 31.5 | 31.5 | agree | t_elm_WideRecord33Test |
| WideRecord33Test | f0032 | 'g' | 'g' | agree | t_elm_WideRecord33Test |
| WideRecord33Test | pattern | (1000,'g') | (1000,'g') | agree | t_elm_WideRecord33Test |
| WideRecord33Test | update | '!' | '!' | agree | t_elm_WideRecord33Test |
| WideRecord33Test | eq self | True | True | agree | t_elm_WideRecord33Test |
| WideRecord33Test | eq updated | False | False | agree | t_elm_WideRecord33Test |
| WideRecord33Test | show | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g' } | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g' } | agree | t_elm_WideRecord33Test |

Elm10: 40 programs, 111 checks, 111 agree.

## Elm11

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| WideRecord40Test | f0000 | 1000 | 1000 | agree | t_elm_WideRecord40Test |
| WideRecord40Test | f0031 | 31.5 | 31.5 | agree | t_elm_WideRecord40Test |
| WideRecord40Test | f0032 | 'g' | 'g' | agree | t_elm_WideRecord40Test |
| WideRecord40Test | f0039 | False | False | agree | t_elm_WideRecord40Test |
| WideRecord40Test | pattern | (1000,False) | (1000,False) | agree | t_elm_WideRecord40Test |
| WideRecord40Test | update | True | True | agree | t_elm_WideRecord40Test |
| WideRecord40Test | eq self | True | True | agree | t_elm_WideRecord40Test |
| WideRecord40Test | eq updated | False | False | agree | t_elm_WideRecord40Test |
| WideRecord40Test | show | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g', f0033 = "33s", f0034 = True, f0035 = 1035, f0036 = 36.5, f0037 = 'l', f0038 = "38s", f0039 = False } | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g', f0033 = "33s", f0034 = True, f0035 = 1035, f0036 = 36.5, f0037 = 'l', f0038 = "38s", f0039 = False } | agree | t_elm_WideRecord40Test |
| WideRecordDecoder26Test | f0000 | Just 1000 | Just 1000 | agree | t_elm_WideRecordDecoder26Test |
| WideRecordDecoder26Test | f0024 | Just 1024 | Just 1024 | agree | t_elm_WideRecordDecoder26Test |
| WideRecordDecoder26Test | f0025 | Just 1025 | Just 1025 | agree | t_elm_WideRecordDecoder26Test |
| WideRecordDecoder30Test | f0000 | Just 1000 | Just 1000 | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0024 | Just 1024 | Just 1024 | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0025 | Just 25.5 | Just 25.5 | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0026 | Just 'a' | Just 'a' | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0027 | Just 1027 | Just 1027 | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0028 | Just "28s" | Just "28s" | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder30Test | f0029 | Just 1029 | Just 1029 | agree | t_elm_WideRecordDecoder30Test |
| WideRecordDecoder70Test | f0000 | Just 1000 | Just 1000 | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0019 | Just False | Just False | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0020 | Just 1020 | Just 1020 | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0024 | Just True | Just True | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0025 | Just 1025 | Just 1025 | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0031 | Just 31.5 | Just 31.5 | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0032 | Just 'g' | Just 'g' | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0033 | Just "33s" | Just "33s" | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0062 | Just 'k' | Just 'k' | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0063 | Just "63s" | Just "63s" | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0064 | Just True | Just True | agree | t_elm_WideRecordDecoder70Test |
| WideRecordDecoder70Test | f0069 | Just False | Just False | agree | t_elm_WideRecordDecoder70Test |
| WideRecordPatternTest | access f27 | 1027 | 1027 | agree | t_elm_WideRecordPatternTest |
| WideRecordPatternTest | access f25 | 1025 | 1025 | agree | t_elm_WideRecordPatternTest |
| WideRecordPatternTest | pattern | 1028025 | 1028025 | agree | t_elm_WideRecordPatternTest |
| WideRecordPatternTest | update f27 | 1028 | 1028 | agree | t_elm_WideRecordPatternTest |
| WideRecordPatternTest | update f26 | 7 | 7 | agree | t_elm_WideRecordPatternTest |
| WideRecordPatternTest | update pattern | 1029025 | 1029025 | agree | t_elm_WideRecordPatternTest |
| WrapperUnionFieldTest | result | 7 | 7 | agree | t_elm_WrapperUnionFieldTest |

Elm11: 6 programs, 38 checks, 38 agree.

## ElmCore01

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| BasicsClampTest | clamp_low | 5 | 5 | agree | t_elm_core_BasicsClampTest |
| BasicsClampTest | clamp_mid | 7 | 7 | agree | t_elm_core_BasicsClampTest |
| BasicsClampTest | clamp_high | 10 | 10 | agree | t_elm_core_BasicsClampTest |
| BasicsClampTest | clamp_float | 3.5 | 3.5 | agree | t_elm_core_BasicsClampTest |
| BasicsIdentityTest | identity_int | 42 | 42 | agree | t_elm_core_BasicsIdentityTest |
| BasicsIdentityTest | identity_string | "hello" | "hello" | agree | t_elm_core_BasicsIdentityTest |
| BasicsIdentityTest | always_result | 99 | 99 | agree | t_elm_core_BasicsIdentityTest |
| BasicsIsNaNTest | nan_check | True | True | agree | t_elm_core_BasicsIsNaNTest |
| BasicsIsNaNTest | not_nan | False | False | agree | t_elm_core_BasicsIsNaNTest |
| BasicsIsNaNTest | inf_check | True | True | agree | t_elm_core_BasicsIsNaNTest |
| BasicsIsNaNTest | not_inf | False | False | agree | t_elm_core_BasicsIsNaNTest |
| BasicsModByTest | mod_pos | 1 | 1 | agree | t_elm_core_BasicsModByTest |
| BasicsModByTest | mod_neg | 2 | 2 | agree | t_elm_core_BasicsModByTest |
| BasicsModByTest | mod_zero | 0 | 0 | agree | t_elm_core_BasicsModByTest |
| BoolNotTest | not1 | False | False | agree | t_elm_core_BoolNotTest |
| BoolNotTest | not2 | True | True | agree | t_elm_core_BoolNotTest |
| BoolXorTest | xor1 | False | False | agree | t_elm_core_BoolXorTest |
| BoolXorTest | xor2 | True | True | agree | t_elm_core_BoolXorTest |
| BoolXorTest | xor3 | True | True | agree | t_elm_core_BoolXorTest |
| BoolXorTest | xor4 | False | False | agree | t_elm_core_BoolXorTest |
| CeilingToIntTest | ceil1 | 3 | 3 | agree | t_elm_core_CeilingToIntTest (native) |
| CeilingToIntTest | ceil2 | -2 | -2 | agree | t_elm_core_CeilingToIntTest (native) |
| CharAstralCodeTest | bmp | 8364 | 8364 | agree | t_elm_core_CharAstralCodeTest |
| CharAstralCodeTest | emoji | 128512 | 128512 | agree | t_elm_core_CharAstralCodeTest |
| CharAstralCodeTest | clef | 119070 | 119070 | agree | t_elm_core_CharAstralCodeTest |
| CharAstralCodeTest | maxcp | 1114111 | 1114111 | agree | t_elm_core_CharAstralCodeTest |
| CharFromCodeTest | char1 | 'A' | 'A' | agree | t_elm_core_CharFromCodeTest |
| CharFromCodeTest | char2 | 'a' | 'a' | agree | t_elm_core_CharFromCodeTest |
| CharFromCodeTest | char3 | '0' | '0' | agree | t_elm_core_CharFromCodeTest |
| CharToCodeTest | code1 | 65 | 65 | agree | t_elm_core_CharToCodeTest |
| CharToCodeTest | code2 | 97 | 97 | agree | t_elm_core_CharToCodeTest |
| CharToCodeTest | code3 | 48 | 48 | agree | t_elm_core_CharToCodeTest |
| CharToCodeThroughFunctionTest | code | 65 | 65 | agree | t_elm_core_CharToCodeThroughFunctionTest |
| ComparableMinMaxTest | minStr | "apple" | "apple" | agree | t_elm_core_ComparableMinMaxTest |
| ComparableMinMaxTest | maxStr | "zebra" | "zebra" | agree | t_elm_core_ComparableMinMaxTest |
| ComparableMinMaxTest | minChar | 'a' | 'a' | agree | t_elm_core_ComparableMinMaxTest |
| ComparableMinMaxTest | maxChar | 'z' | 'z' | agree | t_elm_core_ComparableMinMaxTest |
| CompareCharCaptureTest | sorted | ['a','b','c','d','e'] | ['a','b','c','d','e'] | agree | t_elm_core_CompareCharCaptureTest |
| CompareCharCaptureTest | reverse_sorted | ['e','d','c','b','a'] | ['e','d','c','b','a'] | agree | t_elm_core_CompareCharCaptureTest |
| CompareCharTest | cmp1 | LT | LT | agree | t_elm_core_CompareCharTest |
| CompareCharTest | cmp2 | GT | GT | agree | t_elm_core_CompareCharTest |
| CompareCharTest | cmp3 | EQ | EQ | agree | t_elm_core_CompareCharTest |
| CompareCustomWithEmptyListFieldTest | cmp_ee | EQ | EQ | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareCustomWithEmptyListFieldTest | cmp_eA | LT | LT | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareCustomWithEmptyListFieldTest | cmp_Ae | GT | GT | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareCustomWithEmptyListFieldTest | eq_ee | True | True | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareCustomWithEmptyListFieldTest | eq_eA | False | False | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareCustomWithEmptyListFieldTest | eq_Ae | False | False | agree | t_elm_core_CompareCustomWithEmptyListFieldTest |
| CompareEmptyListTest | ee | EQ | EQ | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | ea | LT | LT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | ae | GT | GT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | eab | LT | LT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | abe | GT | GT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | aa | EQ | EQ | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | ab | LT | LT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | ba | GT | GT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyListTest | aba | GT | GT | agree | t_elm_core_CompareEmptyListTest |
| CompareEmptyStringTest | ee | EQ | EQ | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | ea | LT | LT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | ae | GT | GT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | eab | LT | LT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | abe | GT | GT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | aa | EQ | EQ | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | ab | LT | LT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | ba | GT | GT | agree | t_elm_core_CompareEmptyStringTest |
| CompareEmptyStringTest | aba | GT | GT | agree | t_elm_core_CompareEmptyStringTest |
| CompareFloatCaptureTest | sorted | [1.5,2,2.75,3,4.25] | [1.5,2,2.75,3,4.25] | agree | t_elm_core_CompareFloatCaptureTest |
| CompareFloatCaptureTest | reverse_sorted | [4.25,3,2.75,2,1.5] | [4.25,3,2.75,2,1.5] | agree | t_elm_core_CompareFloatCaptureTest |
| CompareFloatTest | cmp1 | LT | LT | agree | t_elm_core_CompareFloatTest |
| CompareFloatTest | cmp2 | GT | GT | agree | t_elm_core_CompareFloatTest |
| CompareFloatTest | cmp3 | EQ | EQ | agree | t_elm_core_CompareFloatTest |
| CompareIntCaptureTest | sorted | [1,2,3,4,5] | [1,2,3,4,5] | agree | t_elm_core_CompareIntCaptureTest |
| CompareIntCaptureTest | reverse_sorted | [5,4,3,2,1] | [5,4,3,2,1] | agree | t_elm_core_CompareIntCaptureTest |
| CompareIntTest | cmp1 | LT | LT | agree | t_elm_core_CompareIntTest |
| CompareIntTest | cmp2 | GT | GT | agree | t_elm_core_CompareIntTest |
| CompareIntTest | cmp3 | EQ | EQ | agree | t_elm_core_CompareIntTest |
| CompareNestedEmptyListTest | ee | EQ | EQ | agree | t_elm_core_CompareNestedEmptyListTest |
| CompareNestedEmptyListTest | eA | LT | LT | agree | t_elm_core_CompareNestedEmptyListTest |
| CompareNestedEmptyListTest | Ae | GT | GT | agree | t_elm_core_CompareNestedEmptyListTest |
| CompareNestedEmptyListTest | midEmpty | LT | LT | agree | t_elm_core_CompareNestedEmptyListTest |
| CompareNestedEmptyListTest | midNonEmpty | GT | GT | agree | t_elm_core_CompareNestedEmptyListTest |
| CompareRecordWithEmptyListFieldTest | cmp_ee | EQ | EQ | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareRecordWithEmptyListFieldTest | cmp_eA | LT | LT | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareRecordWithEmptyListFieldTest | cmp_Ae | GT | GT | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareRecordWithEmptyListFieldTest | eq_ee | True | True | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareRecordWithEmptyListFieldTest | eq_eA | False | False | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareRecordWithEmptyListFieldTest | eq_Ae | False | False | agree | t_elm_core_CompareRecordWithEmptyListFieldTest |
| CompareStringTest | cmp1 | LT | LT | agree | t_elm_core_CompareStringTest |
| CompareStringTest | cmp2 | GT | GT | agree | t_elm_core_CompareStringTest |
| CompareStringTest | cmp3 | EQ | EQ | agree | t_elm_core_CompareStringTest |
| CompareTupleWithEmptyListNestedTest | ee | EQ | EQ | agree | t_elm_core_CompareTupleWithEmptyListNestedTest |
| CompareTupleWithEmptyListNestedTest | eA | LT | LT | agree | t_elm_core_CompareTupleWithEmptyListNestedTest |
| CompareTupleWithEmptyListNestedTest | Ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyListNestedTest |
| CompareTupleWithEmptyListNestedTest | triple_eA | LT | LT | agree | t_elm_core_CompareTupleWithEmptyListNestedTest |
| CompareTupleWithEmptyListNestedTest | triple_Ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyListNestedTest |
| CompareTupleWithEmptyListTest | ee | EQ | EQ | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | eA | LT | LT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | Ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | eAB | LT | LT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | ABe | GT | GT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | f0_ee | LT | LT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyListTest | f0_Ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyListTest |
| CompareTupleWithEmptyStringTest | ee | EQ | EQ | agree | t_elm_core_CompareTupleWithEmptyStringTest |
| CompareTupleWithEmptyStringTest | ea | LT | LT | agree | t_elm_core_CompareTupleWithEmptyStringTest |
| CompareTupleWithEmptyStringTest | ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyStringTest |
| CompareTupleWithEmptyStringTest | f0_ea | LT | LT | agree | t_elm_core_CompareTupleWithEmptyStringTest |
| CompareTupleWithEmptyStringTest | f0_ae | GT | GT | agree | t_elm_core_CompareTupleWithEmptyStringTest |
| CompilerIssue2362NanTupleEqualityTest | nan == nan | False | False | agree | t_elm_core_CompilerIssue2362NanTupleEqualityTest |
| CompilerIssue2362NanTupleEqualityTest | p == q | False | False | agree | t_elm_core_CompilerIssue2362NanTupleEqualityTest |
| CompilerIssue2362NanTupleEqualityTest | p == p | False | False | agree | t_elm_core_CompilerIssue2362NanTupleEqualityTest |
| CompositionTest | compose1 | 20 | 20 | agree | t_elm_core_CompositionTest |
| CompositionTest | compose2 | 11 | 11 | agree | t_elm_core_CompositionTest |
| CompositionTest | pipe1 | 20 | 20 | agree | t_elm_core_CompositionTest |
| ContainerCompareCharTest | pairLt | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairGt | GT | GT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairEq | EQ | EQ | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairSecondDecides | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairUpperBeforeLower | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairUnicode | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | tripleFirstDecides | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | tripleThirdDecides | GT | GT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | tripleEq | EQ | EQ | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | tripleDigitsBeforeLetters | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listLt | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listShorterIsLess | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listEq | EQ | EQ | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listEmptyIsLeast | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listUnicodeCmp | LT | LT | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairLtOp | True | True | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | pairGeOp | True | True | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | tripleLtOp | True | True | agree | t_elm_core_ContainerCompareCharTest |
| ContainerCompareCharTest | listGtOp | True | True | agree | t_elm_core_ContainerCompareCharTest |
| ContainerEqualityCharTest | pairEqual | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairFirstDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairSecondDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairCaseDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairDigits | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairUnicode | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | pairUnicodeDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | tripleEqual | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | tripleMidDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | tripleMixedCase | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | tripleUnicode | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | listEqual | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | listLenDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | listEmpty | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | listCaseDiff | False | False | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCharTest | listUnicode | True | True | agree | t_elm_core_ContainerEqualityCharTest |
| ContainerEqualityCustomFloatTest | ptEqual | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptXDiff | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptYDiff | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptNegZero | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptNaNFirst | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptNaNSecond | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptPosInf | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | ptInfSign | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | triEqual | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | triMidDiff | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | triAllNegZero | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | triNaNMid | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | triMixedInf | True | True | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityCustomFloatTest | mixedCtorDiff | False | False | agree | t_elm_core_ContainerEqualityCustomFloatTest |
| ContainerEqualityRecordFloatTest | recEqual | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recXDiff | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recYDiff | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recNegZero | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recNaN | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recPosInf | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | recInfSign | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | rec3Equal | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | rec3MidDiff | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | rec3AllNegZero | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | rec3NaNMid | False | False | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityRecordFloatTest | rec3MixedInf | True | True | agree | t_elm_core_ContainerEqualityRecordFloatTest |
| ContainerEqualityStringTest | pairEqual | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairFirstDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairSecondDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairEmpty | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairCaseDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairPrefixDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | pairUnicode | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | tripleEqual | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | tripleMidDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | tripleWithEmpty | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | tripleUnicode | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listEqual | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listLenDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listEmpty | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listEmptyStrings | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listCaseDiff | False | False | agree | t_elm_core_ContainerEqualityStringTest |
| ContainerEqualityStringTest | listUnicode | True | True | agree | t_elm_core_ContainerEqualityStringTest |
| ControlFlowBooleanWithNotTest | testValue | True | True | agree | t_elm_core_ControlFlowBooleanWithNotTest |
| CoreIssue1050NanGreaterThanNanTest | nan > nan | False | False | agree | t_elm_core_CoreIssue1050NanGreaterThanNanTest |
| CoreIssue1050NanGreaterThanNanTest | nan >= nan | False | False | agree | t_elm_core_CoreIssue1050NanGreaterThanNanTest |
| CoreIssue1080ClampNanTest | clamp nan is NaN | True | True | agree | t_elm_core_CoreIssue1080ClampNanTest |
| CoreIssue1080ClampNanTest | clamp nan | NaN | NaN | agree | t_elm_core_CoreIssue1080ClampNanTest |
| CoreIssue1115NanEqualsLiteralZeroTest | nan == 0 | False | False | agree | t_elm_core_CoreIssue1115NanEqualsLiteralZeroTest |
| CoreIssue1115NanEqualsLiteralZeroTest | 0 == nan | False | False | agree | t_elm_core_CoreIssue1115NanEqualsLiteralZeroTest |
| CoreIssue1115NanEqualsLiteralZeroTest | nan == zero | False | False | agree | t_elm_core_CoreIssue1115NanEqualsLiteralZeroTest |
| CoreIssue1150CharToCodeLoneSurrogateTest | {{code: -?[0-9]+(\n\|$)}} |  | code: 65533 | agree | t_elm_core_CoreIssue1150CharToCodeLoneSurrogateTest (native) |
| CoreIssue960PowNegativeExponentIntTest | {{pow: 0(\n\|$)}} |  | pow: 0 | agree | t_elm_core_CoreIssue960PowNegativeExponentIntTest (native) |

ElmCore01: 40 programs, 201 checks, 201 agree.

## ElmCore02

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CoreIssue988NanEqualityReferenceTest | same answer | True | True | agree | t_elm_core_CoreIssue988NanEqualityReferenceTest |
| EqBoxedFastPathTest | strSame | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | strTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | strDiff | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | strNe | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | listSame | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | listTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | listDiff | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | tupleTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | tupleDiff | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | recordTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | recordDiff | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | customTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | customDiff | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | unitEq | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | emptyStrEq | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | emptyListEq | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | boolTT | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | boolTF | False | False | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | boolNe | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqBoxedFastPathTest | nestedTwin | True | True | agree | t_elm_core_EqBoxedFastPathTest |
| EqualityBoolCaseTest | cTT | "yes" | "yes" | agree | t_elm_core_EqualityBoolCaseTest |
| EqualityBoolCaseTest | cTF | "no" | "no" | agree | t_elm_core_EqualityBoolCaseTest |
| EqualityBoolCaseTest | cFT | "no" | "no" | agree | t_elm_core_EqualityBoolCaseTest |
| EqualityBoolCaseTest | cFF | "yes" | "yes" | agree | t_elm_core_EqualityBoolCaseTest |
| EqualityBoolContainerTest | pairTT_TT | True | True | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | pairTT_TF | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | pairTF_TT | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | pairTF_FT | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | tripleTFT_TFT | True | True | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | tripleTFT_TFF | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | listTT_TT | True | True | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | listTF_TF | True | True | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | listTF_FT | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | listTF_TT | False | False | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolContainerTest | listEmpty | True | True | agree | t_elm_core_EqualityBoolContainerTest |
| EqualityBoolIfTest | ifTT | "yes" | "yes" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolIfTest | ifTF | "no" | "no" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolIfTest | ifFT | "no" | "no" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolIfTest | ifFF | "yes" | "yes" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolIfTest | nifTT | "no" | "no" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolIfTest | nifTF | "yes" | "yes" | agree | t_elm_core_EqualityBoolIfTest |
| EqualityBoolMaybeTest | justTT | True | True | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | justTF | False | False | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | justFF | True | True | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | justFT | False | False | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | nothingNothing | True | True | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | justTrueNothing | False | False | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolMaybeTest | nothingJustFalse | False | False | agree | t_elm_core_EqualityBoolMaybeTest |
| EqualityBoolPapTest | isTrueList | [True,False,True,False] | [True,False,True,False] | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolPapTest | isFalseList | [False,True,False,True] | [False,True,False,True] | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolPapTest | filterTrue | [True,True] | [True,True] | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolPapTest | filterFalse | [False,False] | [False,False] | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolPapTest | anyTrue | True | True | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolPapTest | anyFalse | True | True | agree | t_elm_core_EqualityBoolPapTest |
| EqualityBoolRecordTest | recEq | True | True | agree | t_elm_core_EqualityBoolRecordTest |
| EqualityBoolRecordTest | recDiffA | False | False | agree | t_elm_core_EqualityBoolRecordTest |
| EqualityBoolRecordTest | recDiffB | False | False | agree | t_elm_core_EqualityBoolRecordTest |
| EqualityBoolRecordTest | recDiffBoth | False | False | agree | t_elm_core_EqualityBoolRecordTest |
| EqualityBoolRecordTest | recFF_FF | True | True | agree | t_elm_core_EqualityBoolRecordTest |
| EqualityBoolTest | tt | True | True | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | tf | False | False | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | ft | False | False | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | ff | True | True | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | ntt | False | False | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | ntf | True | True | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | nft | True | True | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolTest | nff | False | False | agree | t_elm_core_EqualityBoolTest |
| EqualityBoolVarTest | vTT | True | True | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | vTF | False | False | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | vFT | False | False | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | vFF | True | True | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | hTT | True | True | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | hTF | False | False | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | hFT | False | False | agree | t_elm_core_EqualityBoolVarTest |
| EqualityBoolVarTest | hFF | True | True | agree | t_elm_core_EqualityBoolVarTest |
| EqualityOtherConstantsTest | emptyEmpty | True | True | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | emptyNonEmpty | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | nonEmptyEmpty | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | nilNil | True | True | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | nilCons | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | consNil | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | nothingNothing | True | True | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | nothingJust | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | justNothing | False | False | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityOtherConstantsTest | unitUnit | True | True | agree | t_elm_core_EqualityOtherConstantsTest |
| EqualityTest | eq1 | True | True | agree | t_elm_core_EqualityTest |
| EqualityTest | eq2 | False | False | agree | t_elm_core_EqualityTest |
| EqualityTest | ne1 | True | True | agree | t_elm_core_EqualityTest |
| EqualityTest | ne2 | False | False | agree | t_elm_core_EqualityTest |
| EqualityTest | listEq | True | True | agree | t_elm_core_EqualityTest |
| FloatAbsTest | abs1 | 3.14 | 3.14 | agree | t_elm_core_FloatAbsTest |
| FloatAbsTest | abs2 | 3.14 | 3.14 | agree | t_elm_core_FloatAbsTest |
| FloatAbsTest | abs3 | 0 | 0 | agree | t_elm_core_FloatAbsTest |
| FloatAddTest | add1 | 13 | 13 | agree | t_elm_core_FloatAddTest |
| FloatAddTest | add2 | 0 | 0 | agree | t_elm_core_FloatAddTest |
| FloatAddTest | add3 | -5 | -5 | agree | t_elm_core_FloatAddTest |
| FloatCeilingTest | ceil1 | 3 | 3 | agree | t_elm_core_FloatCeilingTest (native) |
| FloatCeilingTest | ceil2 | 2 | 2 | agree | t_elm_core_FloatCeilingTest (native) |
| FloatCeilingTest | ceil3 | -2 | -2 | agree | t_elm_core_FloatCeilingTest (native) |
| FloatCeilingTest | ceil4 | -2 | -2 | agree | t_elm_core_FloatCeilingTest (native) |
| FloatCompareTest | lt | True | True | agree | t_elm_core_FloatCompareTest |
| FloatCompareTest | gt | True | True | agree | t_elm_core_FloatCompareTest |
| FloatCompareTest | le | True | True | agree | t_elm_core_FloatCompareTest |
| FloatCompareTest | ge | True | True | agree | t_elm_core_FloatCompareTest |
| FloatCompareTest | eq | True | True | agree | t_elm_core_FloatCompareTest |
| FloatCompareTest | ne | True | True | agree | t_elm_core_FloatCompareTest |
| FloatDivTest | div1 | 2.5 | 2.5 | agree | t_elm_core_FloatDivTest |
| FloatDivTest | div2 | -2.5 | -2.5 | agree | t_elm_core_FloatDivTest |
| FloatDivTest | div3 | -2.5 | -2.5 | agree | t_elm_core_FloatDivTest |
| FloatDivTest | div4 | 2.5 | 2.5 | agree | t_elm_core_FloatDivTest |
| FloatFloorTest | floor1 | 2 | 2 | agree | t_elm_core_FloatFloorTest (native) |
| FloatFloorTest | floor2 | 2 | 2 | agree | t_elm_core_FloatFloorTest (native) |
| FloatFloorTest | floor3 | -3 | -3 | agree | t_elm_core_FloatFloorTest (native) |
| FloatFloorTest | floor4 | -3 | -3 | agree | t_elm_core_FloatFloorTest (native) |
| FloatInfinityTest | isInf1 | True | True | agree | t_elm_core_FloatInfinityTest |
| FloatInfinityTest | isInf2 | True | True | agree | t_elm_core_FloatInfinityTest |
| FloatInfinityTest | isInf3 | False | False | agree | t_elm_core_FloatInfinityTest |
| FloatMathAcosTest | testValue | 0 | 0 | agree | t_elm_core_FloatMathAcosTest (native) |
| FloatMathAsinTest | testValue | 0 | 0 | agree | t_elm_core_FloatMathAsinTest (native) |
| FloatMathAtan2Test | testValue | 0.7853981633974483 | 0.7853981633974483 | agree | t_elm_core_FloatMathAtan2Test (native) |
| FloatMathAtanTest | testValue | 0 | 0 | agree | t_elm_core_FloatMathAtanTest (native) |
| FloatMathBasicsETest | testValue | 2.718281828459045 | 2.718281828459045 | agree | t_elm_core_FloatMathBasicsETest |
| FloatMathFloatLessThanTest | testValue | True | True | agree | t_elm_core_FloatMathFloatLessThanTest |
| FloatMathIsNaNTest | testValue | True | True | agree | t_elm_core_FloatMathIsNaNTest |
| FloatMathSin2PlusCos21Test | testValue | 1 | 1 | agree | t_elm_core_FloatMathSin2PlusCos21Test (native) |
| FloatMathTanTest | testValue | 0 | 0 | agree | t_elm_core_FloatMathTanTest (native) |
| FloatMinMaxTest | min1 | 3.14 | 3.14 | agree | t_elm_core_FloatMinMaxTest |
| FloatMinMaxTest | min2 | -5 | -5 | agree | t_elm_core_FloatMinMaxTest |
| FloatMinMaxTest | max1 | 10 | 10 | agree | t_elm_core_FloatMinMaxTest |
| FloatMinMaxTest | max2 | 5 | 5 | agree | t_elm_core_FloatMinMaxTest |
| FloatMulTest | mul1 | 30 | 30 | agree | t_elm_core_FloatMulTest |
| FloatMulTest | mul2 | -15 | -15 | agree | t_elm_core_FloatMulTest |
| FloatMulTest | mul3 | 6 | 6 | agree | t_elm_core_FloatMulTest |
| FloatMulTest | mul4 | 0 | 0 | agree | t_elm_core_FloatMulTest |
| FloatNaNTest | isNaN1 | True | True | agree | t_elm_core_FloatNaNTest |
| FloatNaNTest | isNaN2 | False | False | agree | t_elm_core_FloatNaNTest |
| FloatNaNTest | nanProp | True | True | agree | t_elm_core_FloatNaNTest |
| FloatNaNTest | nanShown | NaN | NaN | agree | t_elm_core_FloatNaNTest |
| FloatNegateTest | neg1 | -3.14 | -3.14 | agree | t_elm_core_FloatNegateTest |
| FloatNegateTest | neg2 | 3.14 | 3.14 | agree | t_elm_core_FloatNegateTest |
| FloatNegateTest | neg3 | 0 | 0 | agree | t_elm_core_FloatNegateTest |
| FloatNegativeZeroTest | eq | True | True | agree | t_elm_core_FloatNegativeZeroTest |
| FloatNegativeZeroTest | div1 | Infinity | Infinity | agree | t_elm_core_FloatNegativeZeroTest |
| FloatNegativeZeroTest | div2 | -Infinity | -Infinity | agree | t_elm_core_FloatNegativeZeroTest |
| FloatPowTest | pow1 | 8 | 8 | agree | t_elm_core_FloatPowTest (native) |
| FloatPowTest | pow2 | 1 | 1 | agree | t_elm_core_FloatPowTest (native) |
| FloatPowTest | pow3 | 1024 | 1024 | agree | t_elm_core_FloatPowTest (native) |
| FloatPowTest | pow4 | 0.5 | 0.5 | agree | t_elm_core_FloatPowTest (native) |
| FloatRoundTest | round1 | 3 | 3 | agree | t_elm_core_FloatRoundTest (native) |
| FloatRoundTest | round2 | 2 | 2 | agree | t_elm_core_FloatRoundTest (native) |
| FloatRoundTest | round3 | -3 | -3 | agree | t_elm_core_FloatRoundTest (native) |
| FloatRoundTest | round4 | 3 | 3 | agree | t_elm_core_FloatRoundTest (native) |
| FloatRoundTest | round5 | 4 | 4 | agree | t_elm_core_FloatRoundTest (native) |
| FloatSqrtTest | sqrt1 | 2 | 2 | agree | t_elm_core_FloatSqrtTest |
| FloatSqrtTest | sqrt2 | 3 | 3 | agree | t_elm_core_FloatSqrtTest |
| FloatSqrtTest | sqrt3 | 0 | 0 | agree | t_elm_core_FloatSqrtTest |
| FloatSubTest | sub1 | 7 | 7 | agree | t_elm_core_FloatSubTest |
| FloatSubTest | sub2 | 10 | 10 | agree | t_elm_core_FloatSubTest |
| FloatSubTest | sub3 | 1 | 1 | agree | t_elm_core_FloatSubTest |
| FloatTruncateTest | trunc1 | 2 | 2 | agree | t_elm_core_FloatTruncateTest (native) |
| FloatTruncateTest | trunc2 | 2 | 2 | agree | t_elm_core_FloatTruncateTest (native) |
| FloatTruncateTest | trunc3 | -2 | -2 | agree | t_elm_core_FloatTruncateTest (native) |
| FloatTruncateTest | trunc4 | -2 | -2 | agree | t_elm_core_FloatTruncateTest (native) |
| FloorToIntTest | floor1 | 2 | 2 | agree | t_elm_core_FloorToIntTest (native) |
| FloorToIntTest | floor2 | -3 | -3 | agree | t_elm_core_FloorToIntTest (native) |
| IntAbsTest | abs1 | 5 | 5 | agree | t_elm_core_IntAbsTest |
| IntAbsTest | abs2 | 5 | 5 | agree | t_elm_core_IntAbsTest |
| IntAbsTest | abs3 | 0 | 0 | agree | t_elm_core_IntAbsTest |

ElmCore02: 40 programs, 169 checks, 169 agree.

## ElmCore03

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| IntAddTest | add1 | 13 | 13 | agree | t_elm_core_IntAddTest |
| IntAddTest | add2 | 0 | 0 | agree | t_elm_core_IntAddTest |
| IntAddTest | add3 | -5 | -5 | agree | t_elm_core_IntAddTest |
| IntCompareTest | lt | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | gt | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | le1 | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | le2 | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | ge1 | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | ge2 | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | eq | True | True | agree | t_elm_core_IntCompareTest |
| IntCompareTest | ne | True | True | agree | t_elm_core_IntCompareTest |
| IntDivByZeroTest | divZero1 | 0 | 0 | agree | t_elm_core_IntDivByZeroTest |
| IntDivByZeroTest | divZero2 | 0 | 0 | agree | t_elm_core_IntDivByZeroTest |
| IntDivTest | div1 | 3 | 3 | agree | t_elm_core_IntDivTest |
| IntDivTest | div2 | -3 | -3 | agree | t_elm_core_IntDivTest |
| IntDivTest | div3 | -3 | -3 | agree | t_elm_core_IntDivTest |
| IntDivTest | div4 | 3 | 3 | agree | t_elm_core_IntDivTest |
| IntMinMaxTest | min1 | 3 | 3 | agree | t_elm_core_IntMinMaxTest |
| IntMinMaxTest | min2 | -5 | -5 | agree | t_elm_core_IntMinMaxTest |
| IntMinMaxTest | max1 | 10 | 10 | agree | t_elm_core_IntMinMaxTest |
| IntMinMaxTest | max2 | 5 | 5 | agree | t_elm_core_IntMinMaxTest |
| IntModByTest | mod1 | 3 | 3 | agree | t_elm_core_IntModByTest |
| IntModByTest | mod2 | 1 | 1 | agree | t_elm_core_IntModByTest |
| IntModByTest | mod3 | 3 | 3 | agree | t_elm_core_IntModByTest |
| IntModByTest | mod4 | 1 | 1 | agree | t_elm_core_IntModByTest |
| IntModByTest | mod5 | 0 | 0 | agree | t_elm_core_IntModByTest |
| IntMulTest | mul1 | 30 | 30 | agree | t_elm_core_IntMulTest |
| IntMulTest | mul2 | -15 | -15 | agree | t_elm_core_IntMulTest |
| IntMulTest | mul3 | 6 | 6 | agree | t_elm_core_IntMulTest |
| IntMulTest | mul4 | 0 | 0 | agree | t_elm_core_IntMulTest |
| IntNegateTest | neg1 | -5 | -5 | agree | t_elm_core_IntNegateTest |
| IntNegateTest | neg2 | 5 | 5 | agree | t_elm_core_IntNegateTest |
| IntNegateTest | neg3 | 0 | 0 | agree | t_elm_core_IntNegateTest |
| IntPowTest | pow1 | 8 | 8 | agree | t_elm_core_IntPowTest (native) |
| IntPowTest | pow2 | 1 | 1 | agree | t_elm_core_IntPowTest (native) |
| IntPowTest | pow3 | 1024 | 1024 | agree | t_elm_core_IntPowTest (native) |
| IntPowTest | pow4 | -8 | -8 | agree | t_elm_core_IntPowTest (native) |
| IntRemainderByTest | rem1 | 3 | 3 | agree | t_elm_core_IntRemainderByTest |
| IntRemainderByTest | rem2 | -3 | -3 | agree | t_elm_core_IntRemainderByTest |
| IntRemainderByTest | rem3 | 3 | 3 | agree | t_elm_core_IntRemainderByTest |
| IntRemainderByTest | rem4 | -3 | -3 | agree | t_elm_core_IntRemainderByTest |
| IntSubTest | sub1 | 7 | 7 | agree | t_elm_core_IntSubTest |
| IntSubTest | sub2 | 10 | 10 | agree | t_elm_core_IntSubTest |
| IntSubTest | sub3 | 1 | 1 | agree | t_elm_core_IntSubTest |
| ListAppendTest | append1 | [1,2,3,4] | [1,2,3,4] | agree | t_elm_core_ListAppendTest |
| ListAppendTest | append_empty | [1,2] | [1,2] | agree | t_elm_core_ListAppendTest |
| ListAppendTest | concat_op | [1,2,3] | [1,2,3] | agree | t_elm_core_ListAppendTest |
| ListConcatTest | append | [1,2,3,4] | [1,2,3,4] | agree | t_elm_core_ListConcatTest |
| ListConcatTest | concat | [1,2,3,4,5,6] | [1,2,3,4,5,6] | agree | t_elm_core_ListConcatTest |
| ListConcatTest | empty | [1,2,3] | [1,2,3] | agree | t_elm_core_ListConcatTest |
| NotEqualBoolCaseTest | cTT | "no" | "no" | agree | t_elm_core_NotEqualBoolCaseTest |
| NotEqualBoolCaseTest | cTF | "yes" | "yes" | agree | t_elm_core_NotEqualBoolCaseTest |
| NotEqualBoolCaseTest | cFT | "yes" | "yes" | agree | t_elm_core_NotEqualBoolCaseTest |
| NotEqualBoolCaseTest | cFF | "no" | "no" | agree | t_elm_core_NotEqualBoolCaseTest |
| NotEqualBoolIfTest | ifTT | "no" | "no" | agree | t_elm_core_NotEqualBoolIfTest |
| NotEqualBoolIfTest | ifTF | "yes" | "yes" | agree | t_elm_core_NotEqualBoolIfTest |
| NotEqualBoolIfTest | ifFT | "yes" | "yes" | agree | t_elm_core_NotEqualBoolIfTest |
| NotEqualBoolIfTest | ifFF | "no" | "no" | agree | t_elm_core_NotEqualBoolIfTest |
| NotEqualBoolMaybeTest | jt_jt | False | False | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | jt_jf | True | True | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | jf_jt | True | True | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | jf_jf | False | False | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | n_jt | True | True | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | n_n | False | False | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolMaybeTest | jt_n | True | True | agree | t_elm_core_NotEqualBoolMaybeTest |
| NotEqualBoolPapTest | isNotTrueList | [False,True,False,True] | [False,True,False,True] | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolPapTest | isNotFalseList | [True,False,True,False] | [True,False,True,False] | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolPapTest | filterNotTrue | [False,False] | [False,False] | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolPapTest | filterNotFalse | [True,True] | [True,True] | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolPapTest | anyNotTrue | True | True | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolPapTest | anyNotFalse | True | True | agree | t_elm_core_NotEqualBoolPapTest |
| NotEqualBoolRecordTest | tt | False | False | agree | t_elm_core_NotEqualBoolRecordTest |
| NotEqualBoolRecordTest | tf | True | True | agree | t_elm_core_NotEqualBoolRecordTest |
| NotEqualBoolRecordTest | ft | True | True | agree | t_elm_core_NotEqualBoolRecordTest |
| NotEqualBoolRecordTest | ff | False | False | agree | t_elm_core_NotEqualBoolRecordTest |
| NotEqualBoolTest | ntt | False | False | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | ntf | True | True | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | nft | True | True | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | nff | False | False | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | bntt | True | True | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | bntf | False | False | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | bnft | False | False | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolTest | bnff | True | True | agree | t_elm_core_NotEqualBoolTest |
| NotEqualBoolVarTest | vTT | False | False | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | vTF | True | True | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | vFT | True | True | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | vFF | False | False | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | hTT | False | False | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | hTF | True | True | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | hFT | True | True | agree | t_elm_core_NotEqualBoolVarTest |
| NotEqualBoolVarTest | hFF | False | False | agree | t_elm_core_NotEqualBoolVarTest |
| OrderingEmptyListPapTest | ltEmpty | [False,True,True] | [False,True,True] | agree | t_elm_core_OrderingEmptyListPapTest |
| OrderingEmptyListPapTest | leEmpty | [True,True,True] | [True,True,True] | agree | t_elm_core_OrderingEmptyListPapTest |
| OrderingEmptyListPapTest | gtEmpty | [False,False,False] | [False,False,False] | agree | t_elm_core_OrderingEmptyListPapTest |
| OrderingEmptyListPapTest | geEmpty | [True,False,False] | [True,False,False] | agree | t_elm_core_OrderingEmptyListPapTest |
| OrderingEmptyListPapTest | cmpEmpty | [EQ,LT,LT] | [EQ,LT,LT] | agree | t_elm_core_OrderingEmptyListPapTest |
| OrderingEmptyListTest | lt_ee | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | lt_ea | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | lt_ae | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | le_ee | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | le_ea | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | le_ae | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | gt_ee | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | gt_ea | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | gt_ae | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | ge_ee | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | ge_ea | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | ge_ae | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | lt_ab | True | True | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyListTest | ge_ab | False | False | agree | t_elm_core_OrderingEmptyListTest |
| OrderingEmptyStringPapTest | ltEmpty | [False,True,True] | [False,True,True] | agree | t_elm_core_OrderingEmptyStringPapTest |
| OrderingEmptyStringPapTest | leEmpty | [True,True,True] | [True,True,True] | agree | t_elm_core_OrderingEmptyStringPapTest |
| OrderingEmptyStringPapTest | gtEmpty | [False,False,False] | [False,False,False] | agree | t_elm_core_OrderingEmptyStringPapTest |
| OrderingEmptyStringPapTest | geEmpty | [True,False,False] | [True,False,False] | agree | t_elm_core_OrderingEmptyStringPapTest |
| OrderingEmptyStringPapTest | cmpEmpty | [EQ,LT,LT] | [EQ,LT,LT] | agree | t_elm_core_OrderingEmptyStringPapTest |
| OrderingEmptyStringTest | lt_ee | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | lt_ea | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | lt_ae | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | le_ee | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | le_ea | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | le_ae | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | gt_ee | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | gt_ea | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | gt_ae | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | ge_ee | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | ge_ea | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | ge_ae | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | lt_ab | True | True | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingEmptyStringTest | ge_ab | False | False | agree | t_elm_core_OrderingEmptyStringTest |
| OrderingMixedCaptureTest | int_lt_count | 3 | 3 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingMixedCaptureTest | int_ge_count | 2 | 2 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingMixedCaptureTest | float_lt_count | 3 | 3 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingMixedCaptureTest | float_ge_count | 2 | 2 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingMixedCaptureTest | char_lt_count | 3 | 3 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingMixedCaptureTest | char_ge_count | 2 | 2 | agree | t_elm_core_OrderingMixedCaptureTest |
| OrderingTupleWithEmptyListTest | lt_ee | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | lt_eA | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | lt_Ae | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | le_ee | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | le_eA | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | le_Ae | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | gt_ee | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | gt_eA | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | gt_Ae | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | ge_ee | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | ge_eA | False | False | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyListTest | ge_Ae | True | True | agree | t_elm_core_OrderingTupleWithEmptyListTest |
| OrderingTupleWithEmptyStringTest | lt_ee | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | lt_eA | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | lt_Ae | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | le_ee | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | le_eA | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | le_Ae | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | gt_ee | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | gt_eA | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | gt_Ae | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | ge_ee | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | ge_eA | False | False | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| OrderingTupleWithEmptyStringTest | ge_Ae | True | True | agree | t_elm_core_OrderingTupleWithEmptyStringTest |
| PipelineTest | pipe1 | 12 | 12 | agree | t_elm_core_PipelineTest |
| PipelineTest | pipe2 | [2,4,6] | [2,4,6] | agree | t_elm_core_PipelineTest |
| PipelineTest | backpipe | 10 | 10 | agree | t_elm_core_PipelineTest |
| RoundToIntTest | round1 | 3 | 3 | agree | t_elm_core_RoundToIntTest (native) |
| RoundToIntTest | round2 | 2 | 2 | agree | t_elm_core_RoundToIntTest (native) |
| RoundToIntTest | round3 | -3 | -3 | agree | t_elm_core_RoundToIntTest (native) |
| StandardA40IntOverflowTest | big * big - big * big + 1 == 1 | True | True | agree | t_elm_core_StandardA40IntOverflowTest |
| StandardA40IntOverflowTest | huge + huge - (huge + huge) + 1 == 1 | True | True | agree | t_elm_core_StandardA40IntOverflowTest |
| StandardA41IntDivisionWideTest | 5000000000 // 1 == 5000000000 | True | True | agree | t_elm_core_StandardA41IntDivisionWideTest |
| StandardA41IntDivisionWideTest | -5000000000 // 1 == -5000000000 | True | True | agree | t_elm_core_StandardA41IntDivisionWideTest |
| StandardA42ModByZeroTest | modBy 0 7 + 1 == 1 | True | True | agree | t_elm_core_StandardA42ModByZeroTest |
| StandardA42ModByZeroTest | modBy 0 -7 + 1 == 1 | True | True | agree | t_elm_core_StandardA42ModByZeroTest |
| StandardA42RemainderByZeroTest | remainderBy 0 7 + 1 == 1 | True | True | agree | t_elm_core_StandardA42RemainderByZeroTest |
| StandardA42RemainderByZeroTest | remainderBy 0 7 | 0 | 0 | agree | t_elm_core_StandardA42RemainderByZeroTest |
| StandardA42ZeroDivisorTest | 3 // 0 | 0 | 0 | agree | t_elm_core_StandardA42ZeroDivisorTest |
| StandardA42ZeroDivisorTest | modBy 0 3 | 0 | 0 | agree | t_elm_core_StandardA42ZeroDivisorTest |
| StandardA42ZeroDivisorTest | remainderBy 0 3 | 0 | 0 | agree | t_elm_core_StandardA42ZeroDivisorTest |
| StandardA43PowNegativeTest | 1 ^ -1 | 1 | 1 | agree | t_elm_core_StandardA43PowNegativeTest |
| StandardA43PowNegativeTest | (-1) ^ -3 | -1 | -1 | agree | t_elm_core_StandardA43PowNegativeTest |
| StandardA43PowNegativeTest | (-1) ^ -2 | 1 | 1 | agree | t_elm_core_StandardA43PowNegativeTest |
| StandardA43PowNegativeTest | 2 ^ -1 + 1 == 1 | True | True | agree | t_elm_core_StandardA43PowNegativeTest |
| StandardA43PowNegativeTest | 0 ^ -1 + 1 == 1 | True | True | agree | t_elm_core_StandardA43PowNegativeTest |
| StandardA44RoundNonFiniteTest | round nan + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44RoundNonFiniteTest | floor nan + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44RoundNonFiniteTest | ceiling nan + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44RoundNonFiniteTest | round inf - round inf + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44RoundNonFiniteTest | floor -inf - floor -inf + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44RoundNonFiniteTest | ceiling inf - ceiling inf + 1 == 1 | True | True | agree | t_elm_core_StandardA44RoundNonFiniteTest (native) |
| StandardA44TruncateWideTest | truncate 3.0e10 >= 2147483647 | True | True | agree | t_elm_core_StandardA44TruncateWideTest (native) |
| StandardA44TruncateWideTest | truncate -3.0e10 <= -2147483648 | True | True | agree | t_elm_core_StandardA44TruncateWideTest (native) |
| StandardA45IntNegativeZeroTest | negate 0 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA45IntNegativeZeroTest | 0 * -1 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA45IntNegativeZeroTest | modBy 4 -4 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA45IntNegativeZeroTest | remainderBy 4 -4 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA45IntNegativeZeroTest | round -0.4 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA45IntNegativeZeroTest | ceiling -0.5 | True | True | agree | t_elm_core_StandardA45IntNegativeZeroTest (native) |
| StandardA46CompareNanTest | compare 1 nan | LT | LT | agree | t_elm_core_StandardA46CompareNanTest |
| StandardA46CompareNanTest | compare nan nan | EQ | EQ | agree | t_elm_core_StandardA46CompareNanTest |
| StandardA46CompareNanTest | compare nan 1 | GT | GT | agree | t_elm_core_StandardA46CompareNanTest |
| StandardA48MinMaxNanTest | min nan 1 is NaN | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | min 1 nan is NaN | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | max nan 1 is NaN | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | max 1 nan is NaN | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | min 0 -0 is -0 | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | min -0 0 is -0 | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | max 0 -0 is +0 | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |
| StandardA48MinMaxNanTest | max -0 0 is +0 | True | True | agree | t_elm_core_StandardA48MinMaxNanTest |

ElmCore03: 40 programs, 206 checks, 206 agree.

## ElmCore04

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| StandardA49ClampTest | clamp 10 0 5 at Float is +0 | True | True | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp nan 1 0.5 is NaN | True | True | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 0 1 -0 is +0 | True | True | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp -1 -0 0 is -0 | True | True | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 10 0 5 at Int | 10 | 10 | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 10 0 20 at Int | 0 | 0 | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 0 10 -5 at Int | 0 | 0 | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 0 10 15 at Int | 10 | 10 | agree | t_elm_core_StandardA49ClampTest |
| StandardA49ClampTest | clamp 0 10 7 at Int | 7 | 7 | agree | t_elm_core_StandardA49ClampTest |
| StandardA51FunctionEqualityTest | compared | True | True | agree | t_elm_core_StandardA51FunctionEqualityTest |
| StandardA53CharOrderTest | compare '😀' 'ﬀ' | GT | GT | agree | t_elm_core_StandardA53CharOrderTest |
| StandardA53CharOrderTest | '😀' > 'ﬀ' | True | True | agree | t_elm_core_StandardA53CharOrderTest |
| StandardA53CharOrderTest | toCode order agrees | True | True | agree | t_elm_core_StandardA53CharOrderTest |
| StandardA53StringOrderTest | compare "😀" "ﬀ" | GT | GT | agree | t_elm_core_StandardA53StringOrderTest |
| StandardA53StringOrderTest | "😀" > "ﬀ" | True | True | agree | t_elm_core_StandardA53StringOrderTest |
| StandardA53StringOrderTest | sorted | ["ﬀ","😀"] | ["ﬀ","😀"] | agree | t_elm_core_StandardA53StringOrderTest |
| StandardA65PowOneTest | 1 ^ inf == 1 | True | True | agree | t_elm_core_StandardA65PowOneTest (native) |
| StandardA65PowOneTest | 1 ^ nan == 1 | True | True | agree | t_elm_core_StandardA65PowOneTest (native) |
| StandardA65PowOneTest | (-1) ^ inf == 1 | True | True | agree | t_elm_core_StandardA65PowOneTest (native) |
| StringConcatContentTest | concat20 | "abcdefghijABCDEFGHIJ" | "abcdefghijABCDEFGHIJ" | agree | t_elm_core_StringConcatContentTest |
| StringConcatContentTest | concat100 | "xyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxy" | "xyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxy" | agree | t_elm_core_StringConcatContentTest |
| StringConcatTest | concat1 | "HelloWorld" | "HelloWorld" | agree | t_elm_core_StringConcatTest |
| StringConcatTest | concat2 | "Hello World" | "Hello World" | agree | t_elm_core_StringConcatTest |
| StringConcatTest | append | "foobar" | "foobar" | agree | t_elm_core_StringConcatTest |
| ToFloatTest | toFloat1 | 42 | 42 | agree | t_elm_core_ToFloatTest |
| ToFloatTest | toFloat2 | -10 | -10 | agree | t_elm_core_ToFloatTest |
| ToFloatTest | toFloat3 | 0 | 0 | agree | t_elm_core_ToFloatTest |
| TruncateToIntTest | trunc1 | 2 | 2 | agree | t_elm_core_TruncateToIntTest (native) |
| TruncateToIntTest | trunc2 | -2 | -2 | agree | t_elm_core_TruncateToIntTest (native) |
| UtilsEqualityCaptureCharTest | eq_count | 2 | 2 | agree | t_elm_core_UtilsEqualityCaptureCharTest |
| UtilsEqualityCaptureCharTest | ne_count | 3 | 3 | agree | t_elm_core_UtilsEqualityCaptureCharTest |
| UtilsEqualityCaptureCharTest | eq_filter | ['x','x'] | ['x','x'] | agree | t_elm_core_UtilsEqualityCaptureCharTest |
| UtilsEqualityCaptureCharTest | ne_filter | ['a','b','c'] | ['a','b','c'] | agree | t_elm_core_UtilsEqualityCaptureCharTest |
| UtilsEqualityCaptureFloatTest | eq_count | 2 | 2 | agree | t_elm_core_UtilsEqualityCaptureFloatTest |
| UtilsEqualityCaptureFloatTest | ne_count | 3 | 3 | agree | t_elm_core_UtilsEqualityCaptureFloatTest |
| UtilsEqualityCaptureFloatTest | eq_filter | [1.5,1.5] | [1.5,1.5] | agree | t_elm_core_UtilsEqualityCaptureFloatTest |
| UtilsEqualityCaptureFloatTest | ne_filter | [0,2,3] | [0,2,3] | agree | t_elm_core_UtilsEqualityCaptureFloatTest |
| UtilsEqualityCaptureIntTest | eq_count | 2 | 2 | agree | t_elm_core_UtilsEqualityCaptureIntTest |
| UtilsEqualityCaptureIntTest | ne_count | 3 | 3 | agree | t_elm_core_UtilsEqualityCaptureIntTest |
| UtilsEqualityCaptureIntTest | eq_filter | [5,5] | [5,5] | agree | t_elm_core_UtilsEqualityCaptureIntTest |
| UtilsEqualityCaptureIntTest | ne_filter | [1,2,3] | [1,2,3] | agree | t_elm_core_UtilsEqualityCaptureIntTest |
| UtilsOrderingCaptureCharTest | lt_filter | ['a','b'] | ['a','b'] | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureCharTest | le_filter | ['a','b','c'] | ['a','b','c'] | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureCharTest | gt_filter | ['d','e'] | ['d','e'] | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureCharTest | ge_filter | ['c','d','e'] | ['c','d','e'] | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureCharTest | count_lt | 2 | 2 | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureCharTest | count_ge | 3 | 3 | agree | t_elm_core_UtilsOrderingCaptureCharTest |
| UtilsOrderingCaptureFloatTest | lt_filter | [1,2] | [1,2] | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureFloatTest | le_filter | [1,2,3] | [1,2,3] | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureFloatTest | gt_filter | [4,5] | [4,5] | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureFloatTest | ge_filter | [3,4,5] | [3,4,5] | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureFloatTest | count_lt | 2 | 2 | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureFloatTest | count_ge | 3 | 3 | agree | t_elm_core_UtilsOrderingCaptureFloatTest |
| UtilsOrderingCaptureIntTest | lt_filter | [1,2] | [1,2] | agree | t_elm_core_UtilsOrderingCaptureIntTest |
| UtilsOrderingCaptureIntTest | le_filter | [1,2,3] | [1,2,3] | agree | t_elm_core_UtilsOrderingCaptureIntTest |
| UtilsOrderingCaptureIntTest | gt_filter | [4,5] | [4,5] | agree | t_elm_core_UtilsOrderingCaptureIntTest |
| UtilsOrderingCaptureIntTest | ge_filter | [3,4,5] | [3,4,5] | agree | t_elm_core_UtilsOrderingCaptureIntTest |
| UtilsOrderingCaptureIntTest | count_lt | 2 | 2 | agree | t_elm_core_UtilsOrderingCaptureIntTest |
| UtilsOrderingCaptureIntTest | count_ge | 3 | 3 | agree | t_elm_core_UtilsOrderingCaptureIntTest |

ElmCore04: 15 programs, 59 checks, 59 agree.

## Worker01

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CoreIssue1141UnusedPortCallBreaksSubscriptionTest | got | "hello" | "hello" | agree | t_elm_CoreIssue1141UnusedPortCallBreaksSubscriptionTest |
| FlagsRecordTest | FlagsRecordTest label | "native-flags" | "native-flags" | agree | t_elm_FlagsRecordTest |
| FlagsRecordTest | FlagsRecordTest count | 43 | 43 | agree | t_elm_FlagsRecordTest |
| FlagsRecordTest | FlagsRecordTest enabled | True | True | agree | t_elm_FlagsRecordTest |
| ListLiteralDebugLogKindTest | fl | 1.5 | 1.5 | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | d | 66108864 | 66108864 or 66108864 | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | c | 'q' | 'q' | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | b | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | capture | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | tuple | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | call | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | sumLit | 132217728 | 132217728 | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | consOp | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | floatLit | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | charLit | ['q','q'] | ['q','q'] | agree | t_elm_ListLiteralDebugLogKindTest |
| ListLiteralDebugLogKindTest | boolLit | True | True | agree | t_elm_ListLiteralDebugLogKindTest |
| NoImportsTest | no imports | 3 | 3 | agree | t_elm_NoImportsTest |
| OutgoingPortTuple3KeepsRunningTest | OutgoingPortTuple3Test | "sent" | "sent" or "after" | agree | t_elm_OutgoingPortTuple3KeepsRunningTest |
| OutgoingPortTuple3KeepsRunningTest | OutgoingPortTuple3Test | "after" | "sent" or "after" | agree | t_elm_OutgoingPortTuple3KeepsRunningTest |
| OutgoingPortTuple3Test | OutgoingPortTuple3Test | "sent" | "sent" | agree | t_elm_OutgoingPortTuple3Test |
| PortAliasEchoTest | PortAliasEchoTest got | { n = 42, s = "hi" } | { n = 42, s = "hi" } | agree | t_elm_PortAliasEchoTest |
| PortAliasEchoTest | PortAliasEchoTest done | "ok" | "ok" | agree | t_elm_PortAliasEchoTest |
| PortEchoBoolTest | PortEchoBoolTest got | True | True or False | agree | t_elm_PortEchoBoolTest |
| PortEchoBoolTest | PortEchoBoolTest got | False | True or False | agree | t_elm_PortEchoBoolTest |
| PortEchoBoolTest | PortEchoBoolTest | "done" | "done" | agree | t_elm_PortEchoBoolTest |
| PortEchoFloatTest | PortEchoFloatTest got | 0 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | 1.5 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | -0.25 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | 0.1 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | 30000000000 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | -1e-7 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest got | 123456.789 | 0 or 1.5 or -0.25 or 0.1 or 30000000000 or -1e-7 or 123456.789 | agree | t_elm_PortEchoFloatTest |
| PortEchoFloatTest | PortEchoFloatTest | "done" | "done" | agree | t_elm_PortEchoFloatTest |
| PortEchoListIntTest | PortEchoListIntTest got | [] | [] or [1,2,3] or [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] | agree | t_elm_PortEchoListIntTest |
| PortEchoListIntTest | PortEchoListIntTest got | [1,2,3] | [] or [1,2,3] or [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] | agree | t_elm_PortEchoListIntTest |
| PortEchoListIntTest | PortEchoListIntTest got | [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] | [] or [1,2,3] or [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] | agree | t_elm_PortEchoListIntTest |
| PortEchoListIntTest | PortEchoListIntTest | "done" | "done" | agree | t_elm_PortEchoListIntTest |
| PortEchoMaybeIntTest | PortEchoMaybeIntTest got | Just 3 | Just 3 or Nothing or Just -7 | agree | t_elm_PortEchoMaybeIntTest |
| PortEchoMaybeIntTest | PortEchoMaybeIntTest got | Nothing | Just 3 or Nothing or Just -7 | agree | t_elm_PortEchoMaybeIntTest |
| PortEchoMaybeIntTest | PortEchoMaybeIntTest got | Just -7 | Just 3 or Nothing or Just -7 | agree | t_elm_PortEchoMaybeIntTest |
| PortEchoMaybeIntTest | PortEchoMaybeIntTest | "done" | "done" | agree | t_elm_PortEchoMaybeIntTest |
| PortEchoNestedTest | PortEchoNestedTest got | [Just (1,["x","y"]),Nothing,Just (2,[])] | [Just (1,["x","y"]),Nothing,Just (2,[])] or [] | agree | t_elm_PortEchoNestedTest |
| PortEchoNestedTest | PortEchoNestedTest got | [] | [Just (1,["x","y"]),Nothing,Just (2,[])] or [] | agree | t_elm_PortEchoNestedTest |
| PortEchoNestedTest | PortEchoNestedTest | "done" | "done" | agree | t_elm_PortEchoNestedTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"hello") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"quote \" back\\slash") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"line\nbreak\ttab") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"café 😀") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest got | (True,"nul\0inside") | (True,"") or (True,"hello") or (True,"quote \" back\\slash") or (True,"line\nbreak\ttab") or (True,"café 😀") or (True,"nul\0inside") | agree | t_elm_PortEchoStringTest |
| PortEchoStringTest | PortEchoStringTest | "done" | "done" | agree | t_elm_PortEchoStringTest |
| PortEchoTest | PortEchoTest got | 42 | 42 | agree | t_elm_PortEchoTest |
| PortEchoTest | PortEchoTest done | "ok" | "ok" | agree | t_elm_PortEchoTest |
| PortEchoTuple2Test | PortEchoTuple2Test got | (1,"one") | (1,"one") or (-2,"") | agree | t_elm_PortEchoTuple2Test |
| PortEchoTuple2Test | PortEchoTuple2Test got | (-2,"") | (1,"one") or (-2,"") | agree | t_elm_PortEchoTuple2Test |
| PortEchoTuple2Test | PortEchoTuple2Test | "done" | "done" | agree | t_elm_PortEchoTuple2Test |
| PortEchoTuple3Test | PortEchoTuple3Test got | (1,2.5,True) | (1,2.5,True) or (0,-0.5,False) | agree | t_elm_PortEchoTuple3Test |
| PortEchoTuple3Test | PortEchoTuple3Test got | (0,-0.5,False) | (1,2.5,True) or (0,-0.5,False) | agree | t_elm_PortEchoTuple3Test |
| PortEchoTuple3Test | PortEchoTuple3Test | "done" | "done" | agree | t_elm_PortEchoTuple3Test |
| PortEchoUnitTest | PortEchoUnitTest got | () | () or () | agree | t_elm_PortEchoUnitTest |
| PortEchoUnitTest | PortEchoUnitTest got | () | () or () | agree | t_elm_PortEchoUnitTest |
| PortEchoUnitTest | PortEchoUnitTest | "done" | "done" | agree | t_elm_PortEchoUnitTest |
| PortIncomingRejectTest | received | "ok" | "ok" | agree | t_elm_PortIncomingRejectTest |
| PortIncomingRejectTest | received: null | (no value) | (not logged) | agree | t_elm_PortIncomingRejectTest (native) |
| StandardA72AbsentFlagsTest | flags | Nothing | Nothing | agree | t_elm_StandardA72AbsentFlagsTest |
| StandardA88PortNegativeZeroTest | 1 / received > 0 | True | True | agree | t_elm_StandardA88PortNegativeZeroTest |
| StandardA88PortNonFiniteTest | got | Nothing | Nothing or Nothing | agree | t_elm_StandardA88PortNonFiniteTest |
| StandardA88PortNonFiniteTest | got | Nothing | Nothing or Nothing | agree | t_elm_StandardA88PortNonFiniteTest |
| StandardA88PortNonFiniteTest | Just | (no value) | (not logged) | agree | t_elm_StandardA88PortNonFiniteTest (native) |
| CmdMapComposeTest | message | "x then g then f" | "x then g then f" | agree | t_elm_core_CmdMapComposeTest |
| CoreIssue1110PortDeclarationOrderTest | got | "hello" | "hello" | agree | t_elm_core_CoreIssue1110PortDeclarationOrderTest |
| CoreIssue1154PortSubscribedWithCmdTest | got | "hello" | "hello" | agree | t_elm_core_CoreIssue1154PortSubscribedWithCmdTest |
| CoreIssue955KillProcessTwiceTest | killed twice | () | () | agree | t_elm_core_CoreIssue955KillProcessTwiceTest |
| ProcessPrimitiveOutcomeTest | sleep gave | () | () | agree | t_elm_core_ProcessPrimitiveOutcomeTest |
| ProcessPrimitiveOutcomeTest | kill gave | () | () | agree | t_elm_core_ProcessPrimitiveOutcomeTest |
| ProcessSpawnKillHalfTest | spawnKill | "fired 1" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnKillHalfTest | spawnKill | "fired 3" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnKillHalfTest | spawnKill | "fired 5" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnKillHalfTest | spawnKill | "fired 7" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnKillHalfTest | spawnKill | "fired 9" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnKillHalfTest | spawnKill | "done" | "fired 1" or "fired 3" or "fired 5" or "fired 7" or "fired 9" or "done" | agree | t_elm_core_ProcessSpawnKillHalfTest (native) |
| ProcessSpawnRecursiveTest | recurse | "spawned 1" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "spawned 2" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "spawned 3" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "spawned 4" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "spawned 5" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "bottom" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnRecursiveTest | recurse | "done" | "spawned 1" or "spawned 2" or "spawned 3" or "spawned 4" or "spawned 5" or "bottom" or "done" | agree | t_elm_core_ProcessSpawnRecursiveTest (native) |
| ProcessSpawnedFailureEndsTest | spawned | True | True | agree | t_elm_core_ProcessSpawnedFailureEndsTest |
| ProcessSpawnedFailureEndsTest | still running | True | True | agree | t_elm_core_ProcessSpawnedFailureEndsTest |
| ProcessYieldThrashingTest | yield | "A 1" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "A 2" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "A 3" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "A 4" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "A 5" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "B 1" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "B 2" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "B 3" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "B 4" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "B 5" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| ProcessYieldThrashingTest | yield | "done" | "A 1" or "A 2" or "B 1" or "A 3" or "B 2" or "A 4" or "B 3" or "A 5" or "B 4" or "B 5" or "done" | agree | t_elm_core_ProcessYieldThrashingTest (native) |
| StandardA81SleepBeyond32BitsTest | checked after 200 ms | () | () | agree | t_elm_core_StandardA81SleepBeyond32BitsTest |
| TaskAttemptErrorTest | ok | 42 | 42 | agree | t_elm_core_TaskAttemptErrorTest |
| TaskAttemptErrorTest | err | "boom" | "boom" | agree | t_elm_core_TaskAttemptErrorTest |
| TaskOnErrorCascadeTest | onerr | "recovered 1" | "recovered 1" or "recovered 2" or "recovered 3" or "final: 60" | agree | t_elm_core_TaskOnErrorCascadeTest (native) |
| TaskOnErrorCascadeTest | onerr | "recovered 2" | "recovered 1" or "recovered 2" or "recovered 3" or "final: 60" | agree | t_elm_core_TaskOnErrorCascadeTest (native) |
| TaskOnErrorCascadeTest | onerr | "recovered 3" | "recovered 1" or "recovered 2" or "recovered 3" or "final: 60" | agree | t_elm_core_TaskOnErrorCascadeTest (native) |
| TaskOnErrorCascadeTest | onerr | "final: 60" | "recovered 1" or "recovered 2" or "recovered 3" or "final: 60" | agree | t_elm_core_TaskOnErrorCascadeTest (native) |
| TaskOnErrorInnerTest | failed then handled | 70 | 70 | agree | t_elm_core_TaskOnErrorInnerTest |
| TaskOnErrorInnerTest | succeeded through | 5 | 5 | agree | t_elm_core_TaskOnErrorInnerTest |
| TaskOnErrorSucceedTest | result | 1 | 1 | agree | t_elm_core_TaskOnErrorSucceedTest |
| TaskOnErrorSucceedTest | handler called | (no value) | (not logged) | agree | t_elm_core_TaskOnErrorSucceedTest (native) |
| TaskPerformValueTest | a | 42 | 42 | agree | t_elm_core_TaskPerformValueTest |
| TaskPerformValueTest | b | "nullary ok" | "nullary ok" | agree | t_elm_core_TaskPerformValueTest |
| TaskPerformValueTest | c | -7 | -7 | agree | t_elm_core_TaskPerformValueTest |
| TaskPerformValueTest | d | "hello" | "hello" | agree | t_elm_core_TaskPerformValueTest |
| TaskSucceedAsArgTest | got | 7 | 7 | agree | t_elm_core_TaskSucceedAsArgTest |
| TimerEffectTest | TimerEffectTest | "fired 1" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |
| TimerEffectTest | TimerEffectTest | "fired 2" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |
| TimerEffectTest | TimerEffectTest | "fired 3" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |
| TimerEffectTest | TimerEffectTest | "fired 4" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |
| TimerEffectTest | TimerEffectTest | "fired 5" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |
| TimerEffectTest | TimerEffectTest | "done" | "fired 1" or "fired 2" or "fired 3" or "fired 4" or "fired 5" or "done" | agree | t_elm_core_TimerEffectTest (native) |

Worker01: 38 programs, 123 checks, 123 agree.

Total: 1708 checks, 1708 agree, 0 diverge (0 known); 1497 checks by decide +kernel, 209 by native_decide, in 579 program theorems.
