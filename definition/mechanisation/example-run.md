# Standard Elm mechanisation: example run

Programs: 487, in 13 shards; checks: 1477.

## Elm01

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| AccessorFunctionFieldInListTest | results | [11,20] | [11,20] | agree |  |
| AccessorFunctionFieldTailCallTest | results | [2,11,142,42] | [2,11,142,42] | agree |  |
| AccessorPlaceholderAccessorOfAFunctionFieldPassedInTailCallsTest | testValue | 8 | 8 | agree | kc_Elm01_0 |
| AccessorToLocalFuncTest | result | 42 | 42 | agree | kc_Elm01_1 |
| AccessorVariableTest | via_var | 42 | 42 | agree | kc_Elm01_2 |
| AccessorVariableTest | mapped | [10,20,30] | [10,20,30] | agree |  |
| AccessorVariableTest | person_name | "Alice" | "Alice" | agree | kc_Elm01_3 |
| AccessorVariableTest | company_name | "ACME" | "ACME" | agree | kc_Elm01_4 |
| AliasForwardTest | dupInt | 3 | 3 | agree |  |
| AliasForwardTest | dupStr | "a!!" | "a!!" | agree |  |
| AliasForwardTest | foldInt | 6 | 6 | agree |  |
| AliasForwardTest | foldFloat | 45 | 45 | agree |  |
| AliasForwardTest | mapPartial | 5 | 5 | agree |  |
| AliasForwardTest | value | 4 | 4 | agree |  |
| AnnotatedLetRecFnResultTest | AnnotatedLetRecFnResultTest | 16 | 16 | agree | kc_Elm01_5 |
| AnonymousFunctionTest | lambda1 | [2,4,6] | [2,4,6] | agree |  |
| AnonymousFunctionTest | lambda2 | 15 | 15 | agree | kc_Elm01_6 |
| AnonymousFunctionTest | lambda3 | [2,4] | [2,4] | agree |  |
| AppendTypeSplitTest | strs | "foobar" | "foobar" | agree | kc_Elm01_7 |
| AppendTypeSplitTest | strEmptyR | "foo" | "foo" | agree | kc_Elm01_8 |
| AppendTypeSplitTest | strEmptyL | "foo" | "foo" | agree | kc_Elm01_9 |
| AppendTypeSplitTest | strBothEmpty | "" | "" | agree | kc_Elm01_10 |
| AppendTypeSplitTest | ropeEq | True | True | agree | kc_Elm01_11 |
| AppendTypeSplitTest | ropeNeq | False | False | agree | kc_Elm01_12 |
| AppendTypeSplitTest | lists | [1,2,3,4] | [1,2,3,4] | agree |  |
| AppendTypeSplitTest | listEmptyR | [1,2] | [1,2] | agree |  |
| AppendTypeSplitTest | listEmptyL | [1,2] | [1,2] | agree |  |
| AppendTypeSplitTest | listBothEmpty | [] | [] | agree |  |
| AppendTypeSplitTest | chunkAppend | [2,4,6,1] | [2,4,6,1] | agree |  |
| AppendTypeSplitTest | nested | "abcdef" | "abcdef" | agree | kc_Elm01_13 |
| AppendTypeSplitTest | polyStr | "hihi" | "hihi" | agree | kc_Elm01_14 |
| AppendTypeSplitTest | polyList | [7,7] | [7,7] | agree |  |
| AstralCharCasePatternTest | a | "other" | "other" | agree | kc_Elm01_15 |
| AstralCharCasePatternTest | euro | "euro" | "euro" | agree | kc_Elm01_16 |
| AstralCharCasePatternTest | escape | "grin" | "grin" | agree | kc_Elm01_17 |
| AstralCharCasePatternTest | literal | "grin" | "grin" | agree | kc_Elm01_18 |
| AstralCharLiteralTest | astral | 128512 | 128512 | agree | kc_Elm01_19 |
| AstralCharLiteralTest | bmp | 8364 | 8364 | agree | kc_Elm01_20 |
| AstralCharLiteralTest | sameAsWritten | True | True | agree | kc_Elm01_21 |
| BoolAndTest | and1 | True | True | agree | kc_Elm01_22 |
| BoolAndTest | and2 | False | False | agree | kc_Elm01_23 |
| BoolAndTest | and3 | False | False | agree | kc_Elm01_24 |
| BoolAndTest | and4 | False | False | agree | kc_Elm01_25 |
| BoolOrTest | or1 | True | True | agree | kc_Elm01_26 |
| BoolOrTest | or2 | True | True | agree | kc_Elm01_27 |
| BoolOrTest | or3 | True | True | agree | kc_Elm01_28 |
| BoolOrTest | or4 | False | False | agree | kc_Elm01_29 |
| BoolShortCircuitParserIdiomTest | peek at past-end | "none" | "none" | agree |  |
| BoolShortCircuitParserIdiomTest | peek at first | 'H' | 'H' | agree |  |
| BoolShortCircuitTest | shortAnd | False | False | agree | kc_Elm01_30 |
| BoolShortCircuitTest | shortOr | True | True | agree | kc_Elm01_31 |
| CapturedStagedFuncCallTest | direct | 15 | 15 | agree | kc_Elm01_32 |
| CapturedStagedFuncCallTest | viaCapture | 15 | 15 | agree | kc_Elm01_33 |
| CaseAsPatternTest | as1 | 0 | 0 | agree | kc_Elm01_34 |
| CaseAsPatternTest | as2 | 3 | 3 | agree | kc_Elm01_35 |
| CaseAsPatternTest | as3 | 6 | 6 | agree | kc_Elm01_36 |
| CaseBoolTest | case1 | "yes" | "yes" | agree | kc_Elm01_37 |
| CaseBoolTest | case2 | "no" | "no" | agree | kc_Elm01_38 |
| CaseBranchSelectionTest | classify | ["zero","one","pair 2 3","other 9"] | ["zero","one","pair 2 3","other 9"] | agree |  |
| CaseBranchSelectionTest | first match wins | "specific" | "specific" | agree |  |
| CaseCharManyBranchTest | d0 | 0 | 0 | agree | kc_Elm01_39 |
| CaseCharManyBranchTest | d5 | 5 | 5 | agree | kc_Elm01_40 |
| CaseCharManyBranchTest | d9 | 9 | 9 | agree | kc_Elm01_41 |
| CaseCharManyBranchTest | other | -1 | -1 | agree | kc_Elm01_42 |
| CaseCharTest | char1 | "vowel a" | "vowel a" | agree | kc_Elm01_43 |
| CaseCharTest | char2 | "vowel e" | "vowel e" | agree | kc_Elm01_44 |
| CaseCharTest | char3 | "other" | "other" | agree | kc_Elm01_45 |
| CaseCharTest | char4 | "other" | "other" | agree | kc_Elm01_46 |
| CaseCtorArgPatternTest | id | 30 | 30 | agree | kc_Elm01_47 |
| CaseCtorArgPatternTest | age | 25 | 25 | agree | kc_Elm01_48 |
| CaseCustomType4Test | dir1 | "up" | "up" | agree | kc_Elm01_49 |
| CaseCustomType4Test | dir2 | "down" | "down" | agree | kc_Elm01_50 |
| CaseCustomType4Test | dir3 | "left" | "left" | agree | kc_Elm01_51 |
| CaseCustomType4Test | dir4 | "right" | "right" | agree | kc_Elm01_52 |
| CaseCustomType4WildcardTest | card1 | "hearts" | "hearts" | agree | kc_Elm01_53 |
| CaseCustomType4WildcardTest | card2 | "spades" | "spades" | agree | kc_Elm01_54 |
| CaseCustomType4WildcardTest | card3 | "other" | "other" | agree | kc_Elm01_55 |
| CaseCustomType4WildcardTest | card4 | "other" | "other" | agree | kc_Elm01_56 |
| CaseCustomTypeTest | shape1 | 100 | 100 | agree | kc_Elm01_57 |
| CaseCustomTypeTest | shape2 | 50 | 50 | agree | kc_Elm01_58 |
| CaseDeepNestTest | r1 | "x=0,y=0" | "x=0,y=0" | agree | kc_Elm01_59 |
| CaseDeepNestTest | r2 | "x=0,y=other" | "x=0,y=other" | agree | kc_Elm01_60 |
| CaseDeepNestTest | r3 | "x=1,y=0" | "x=1,y=0" | agree | kc_Elm01_61 |
| CaseDeepNestTest | r4 | "x=other" | "x=other" | agree | kc_Elm01_62 |
| CaseDeepNestTest | triple | "all zero" | "all zero" | agree | kc_Elm01_63 |
| CaseDeepNestTest | triple2 | "z=other" | "z=other" | agree | kc_Elm01_64 |
| CaseDeeplyNestedTest | deep1 | "all" | "all" | agree | kc_Elm01_65 |
| CaseDeeplyNestedTest | deep2 | "two" | "two" | agree | kc_Elm01_66 |
| CaseDefaultTest | default1 | "special" | "special" | agree | kc_Elm01_67 |
| CaseDefaultTest | default2 | "normal" | "normal" | agree | kc_Elm01_68 |
| CaseDefaultTest | default3 | "normal" | "normal" | agree | kc_Elm01_69 |
| CaseGuardLikeTest | grade1 | "A" | "A" | agree | kc_Elm01_70 |
| CaseGuardLikeTest | grade2 | "B" | "B" | agree | kc_Elm01_71 |
| CaseGuardLikeTest | grade3 | "C" | "C" | agree | kc_Elm01_72 |
| CaseGuardLikeTest | grade4 | "F" | "F" | agree | kc_Elm01_73 |
| CaseInLambdaTest | lambda1 | "yes" | "yes" | agree | kc_Elm01_74 |
| CaseInLambdaTest | lambda2 | "no" | "no" | agree | kc_Elm01_75 |
| CaseInLambdaTest | lambda3 | "yes" | "yes" | agree | kc_Elm01_76 |
| CaseInLetTest | let1 | "positive" | "positive" | agree | kc_Elm01_77 |
| CaseInLetTest | let2 | "zero" | "zero" | agree | kc_Elm01_78 |
| CaseInLetTest | let3 | "negative" | "negative" | agree | kc_Elm01_79 |
| CaseIntTest | case1 | "one" | "one" | agree | kc_Elm01_80 |
| CaseIntTest | case2 | "two" | "two" | agree | kc_Elm01_81 |
| CaseIntTest | case3 | "other" | "other" | agree | kc_Elm01_82 |
| CaseListConsTest | sum1 | 0 | 0 | agree | kc_Elm01_83 |
| CaseListConsTest | sum2 | 1 | 1 | agree | kc_Elm01_84 |
| CaseListConsTest | sum3 | 6 | 6 | agree | kc_Elm01_85 |
| CaseListTest | case1 | "empty" | "empty" | agree | kc_Elm01_86 |
| CaseListTest | case2 | "one" | "one" | agree | kc_Elm01_87 |
| CaseListTest | case3 | "many" | "many" | agree | kc_Elm01_88 |
| CaseListThreeWayTest | desc1 | "empty" | "empty" | agree |  |
| CaseListThreeWayTest | desc2 | "single: 42" | "single: 42" | agree |  |
| CaseListThreeWayTest | desc3 | "multiple: 1" | "multiple: 1" | agree |  |
| CaseManyBranchesTest | day1 | "Monday" | "Monday" | agree | kc_Elm01_89 |
| CaseManyBranchesTest | day5 | "Friday" | "Friday" | agree | kc_Elm01_90 |
| CaseManyBranchesTest | day7 | "Sunday" | "Sunday" | agree | kc_Elm01_91 |
| CaseMaybePairTest | both | 7 | 7 | agree | kc_Elm01_92 |
| CaseMaybePairTest | first | 3 | 3 | agree | kc_Elm01_93 |
| CaseMaybePairTest | second | 4 | 4 | agree | kc_Elm01_94 |
| CaseMaybePairTest | neither | 0 | 0 | agree | kc_Elm01_95 |
| CaseMaybeTest | case1 | 42 | 42 | agree | kc_Elm01_96 |
| CaseMaybeTest | case2 | -1 | -1 | agree | kc_Elm01_97 |
| CaseMixedPatternTest | head | 42 | 42 | agree | kc_Elm01_98 |
| CaseMixedPatternTest | empty | 0 | 0 | agree | kc_Elm01_99 |
| CaseMixedPatternTest | pair_head | 10 | 10 | agree | kc_Elm01_100 |
| CaseMixedPatternTest | pair_empty | -1 | -1 | agree | kc_Elm01_101 |
| CaseMixedPatternTest | nested | 99 | 99 | agree | kc_Elm01_102 |
| CaseMultiFieldExtractTest | point1 | 3 | 3 | agree | kc_Elm01_103 |
| CaseMultiFieldExtractTest | point2 | 6 | 6 | agree | kc_Elm01_104 |
| CaseMultiFieldExtractTest | rect1 | 50 | 50 | agree | kc_Elm01_105 |

Elm01: 40 programs, 130 checks, 130 agree.

## Elm02

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CaseNestedCtorTest | single | 42 | 42 | agree | kc_Elm02_0 |
| CaseNestedCtorTest | double | 3 | 3 | agree | kc_Elm02_1 |
| CaseNestedRecordAccessTest | test1 | True | True | agree | kc_Elm02_2 |
| CaseNestedRecordAccessTest | test2 | False | False | agree | kc_Elm02_3 |
| CaseNestedRecordAccessTest | test3 | True | True | agree | kc_Elm02_4 |
| CaseNestedRecordAccessTest | test4 | True | True | agree | kc_Elm02_5 |
| CaseNestedTest | nested1 | "both" | "both" | agree | kc_Elm02_6 |
| CaseNestedTest | nested2 | "first" | "first" | agree | kc_Elm02_7 |
| CaseNestedTest | nested3 | "second" | "second" | agree | kc_Elm02_8 |
| CaseNestedTest | nested4 | "neither" | "neither" | agree | kc_Elm02_9 |
| CaseOrderTest | ord1 | "less" | "less" | agree | kc_Elm02_10 |
| CaseOrderTest | ord2 | "equal" | "equal" | agree | kc_Elm02_11 |
| CaseOrderTest | ord3 | "greater" | "greater" | agree | kc_Elm02_12 |
| CaseReturnFunctionTest | op1 | 7 | 7 | agree | kc_Elm02_13 |
| CaseReturnFunctionTest | op2 | 3 | 3 | agree | kc_Elm02_14 |
| CaseReturnFunctionTest | op3 | 10 | 10 | agree | kc_Elm02_15 |
| CaseReturningLambdaTest | r1 | 6 | 6 | agree | kc_Elm02_16 |
| CaseReturningLambdaTest | r2 | 5 | 5 | agree | kc_Elm02_17 |
| CaseReturningLambdaTest | r3 | 0 | 0 | agree | kc_Elm02_18 |
| CaseReturningLambdaTest | r4 | 99 | 99 | agree | kc_Elm02_19 |
| CaseSharedBranchTest | r1 | "greeting" | "greeting" | agree | kc_Elm02_20 |
| CaseSharedBranchTest | r2 | "farewell" | "farewell" | agree | kc_Elm02_21 |
| CaseSharedBranchTest | r3 | "unknown cmd" | "unknown cmd" | agree | kc_Elm02_22 |
| CaseSharedBranchTest | r4 | "fixed" | "fixed" | agree | kc_Elm02_23 |
| CaseSingleCtorBoolMultiTypeTest | nested_true | "split" | "split" | agree | kc_Elm02_24 |
| CaseSingleCtorBoolMultiTypeTest | nested_false | "join" | "join" | agree | kc_Elm02_25 |
| CaseSingleCtorBoolMultiTypeTest | extract_true | True | True | agree | kc_Elm02_26 |
| CaseSingleCtorBoolMultiTypeTest | extract_false | False | False | agree | kc_Elm02_27 |
| CaseSingleCtorBoolMultiTypeTest | wrap_int | 42 | 42 | agree | kc_Elm02_28 |
| CaseSingleCtorBoolTest | nested_true | "split" | "split" | agree | kc_Elm02_29 |
| CaseSingleCtorBoolTest | nested_false | "join" | "join" | agree | kc_Elm02_30 |
| CaseSingleCtorBoolTest | extract_true | True | True | agree | kc_Elm02_31 |
| CaseSingleCtorBoolTest | extract_false | False | False | agree | kc_Elm02_32 |
| CaseStringEmptyPatternTest | empty | "yes" | "yes" | agree | kc_Elm02_33 |
| CaseStringEmptyPatternTest | Y | "yes" | "yes" | agree | kc_Elm02_34 |
| CaseStringEmptyPatternTest | y | "yes" | "yes" | agree | kc_Elm02_35 |
| CaseStringEmptyPatternTest | n | "no" | "no" | agree | kc_Elm02_36 |
| CaseStringEmptyPatternTest | maybe | "retry" | "retry" | agree | kc_Elm02_37 |
| CaseStringEscapeTest | esc1 | "newline" | "newline" | agree | kc_Elm02_38 |
| CaseStringEscapeTest | esc2 | "tab" | "tab" | agree | kc_Elm02_39 |
| CaseStringEscapeTest | esc3 | "quote" | "quote" | agree | kc_Elm02_40 |
| CaseStringEscapeTest | esc4 | "other" | "other" | agree | kc_Elm02_41 |
| CaseStringManyBranchTest | d1 | "Monday" | "Monday" | agree | kc_Elm02_42 |
| CaseStringManyBranchTest | d4 | "Thursday" | "Thursday" | agree | kc_Elm02_43 |
| CaseStringManyBranchTest | d7 | "Sunday" | "Sunday" | agree | kc_Elm02_44 |
| CaseStringManyBranchTest | other | "unknown" | "unknown" | agree | kc_Elm02_45 |
| CaseStringTest | case1 | 1 | 1 | agree | kc_Elm02_46 |
| CaseStringTest | case2 | 2 | 2 | agree | kc_Elm02_47 |
| CaseStringTest | case3 | 0 | 0 | agree | kc_Elm02_48 |
| CaseTreeTest | tree1 | 0 | 0 | agree | kc_Elm02_49 |
| CaseTreeTest | tree2 | 1 | 1 | agree | kc_Elm02_50 |
| CaseTreeTest | tree3 | 3 | 3 | agree | kc_Elm02_51 |
| CaseTripleTest | triple1 | "all zero" | "all zero" | agree | kc_Elm02_52 |
| CaseTripleTest | triple2 | "x zero" | "x zero" | agree | kc_Elm02_53 |
| CaseTripleTest | triple3 | "z zero" | "z zero" | agree | kc_Elm02_54 |
| CaseTripleTest | triple4 | "none zero" | "none zero" | agree | kc_Elm02_55 |
| CaseTupleLiteralTest | origin | "origin" | "origin" | agree | kc_Elm02_56 |
| CaseTupleLiteralTest | xaxis | "x-axis" | "x-axis" | agree | kc_Elm02_57 |
| CaseTupleLiteralTest | yaxis | "y-axis" | "y-axis" | agree | kc_Elm02_58 |
| CaseTupleLiteralTest | unit | "unit" | "unit" | agree | kc_Elm02_59 |
| CaseTupleLiteralTest | general | "general" | "general" | agree | kc_Elm02_60 |
| CaseTupleTest | pair1 | "both zero" | "both zero" | agree | kc_Elm02_61 |
| CaseTupleTest | pair2 | "x is zero" | "x is zero" | agree | kc_Elm02_62 |
| CaseTupleTest | pair3 | "y is zero" | "y is zero" | agree | kc_Elm02_63 |
| CaseTupleTest | pair4 | "neither zero" | "neither zero" | agree | kc_Elm02_64 |
| CaseUnicodeCharTest | char1 | "greek alpha" | "greek alpha" | agree | kc_Elm02_65 |
| CaseUnicodeCharTest | char2 | "greek beta" | "greek beta" | agree | kc_Elm02_66 |
| CaseUnicodeCharTest | char3 | "cjk" | "cjk" | agree | kc_Elm02_67 |
| CaseUnicodeCharTest | char4 | "other" | "other" | agree | kc_Elm02_68 |
| CharAstralClosureCaptureTest | cap_add | [128513,98] | [128513,98] | agree |  |
| CharAstralClosureCaptureTest | cap_return | [128512,119070] | [128512,119070] | agree |  |
| CharAstralClosureCaptureTest | pap_pairs | [128513,128514] | [128513,128514] | agree |  |
| CharAstralCustomFieldTest | box_code | 128512 | 128512 | agree | kc_Elm02_69 |
| CharAstralCustomFieldTest | shape_codes | [128512,119070,-1] | [128512,119070,-1] | agree |  |
| CharAstralRecordFieldTest | rec_c | 128512 | 128512 | agree | kc_Elm02_70 |
| CharAstralRecordFieldTest | rec_n | 7 | 7 | agree | kc_Elm02_71 |
| CharAstralRecordFieldTest | rec_updated | 119070 | 119070 | agree | kc_Elm02_72 |
| CharAstralRecordFieldTest | rec_eq | True | True | agree | kc_Elm02_73 |
| CharAstralTupleTest | tup2_code | 128512 | 128512 | agree | kc_Elm02_74 |
| CharAstralTupleTest | tup3_code | 119070 | 119070 | agree | kc_Elm02_75 |
| CharCaptureEscapedTailDefTest | hit | True | True | agree | kc_Elm02_76 |
| CharCaptureEscapedTailDefTest | miss | False | False | agree | kc_Elm02_77 |
| CharCaptureEscapedTailDefTest | both | True | True | agree | kc_Elm02_78 |
| CharLiteralPatternMatchMinimalTest | m1_bareChar | "y" | "y" | agree | kc_Elm02_79 |
| CharLiteralPatternMatchMinimalTest | m2_charInTuple | "y" | "y" | agree | kc_Elm02_80 |
| CharLiteralPatternMatchMinimalTest | m3_charInMaybe | "y" | "y" | agree | kc_Elm02_81 |
| CharLiteralPatternMatchMinimalTest | m4_charInMaybeTuple | "y" | "y" | agree | kc_Elm02_82 |
| CharLiteralPatternMatchVariousTest | dquote | "y" | "y" | agree | kc_Elm02_83 |
| CharLiteralPatternMatchVariousTest | lbrace | "y" | "y" | agree | kc_Elm02_84 |
| CharLiteralPatternMatchVariousTest | lowerA | "y" | "y" | agree | kc_Elm02_85 |
| CharLiteralPatternMatchVariousTest | backslash | "y" | "y" | agree | kc_Elm02_86 |
| CharLiteralPatternMatchVariousTest | newline | "y" | "y" | agree | kc_Elm02_87 |
| CharLiteralPatternMatchVariousTest | digit0 | "y" | "y" | agree | kc_Elm02_88 |
| CharLiteralPatternMatchVariousTest | space | "y" | "y" | agree | kc_Elm02_89 |
| CharUnicodeTest | code1 | 955 | 955 | agree | kc_Elm02_90 |
| CharUnicodeTest | code2 | 8364 | 8364 | agree | kc_Elm02_91 |
| ClosureCapture01Test | unwrap1 | 42 | 42 | agree | kc_Elm02_92 |
| ClosureCapture01Test | unwrap2 | 99 | 99 | agree | kc_Elm02_93 |
| ClosureCapture02Test | just | "hello" | "hello" | agree | kc_Elm02_94 |
| ClosureCapture02Test | nothing | "none" | "none" | agree | kc_Elm02_95 |
| ClosureCapture03Test | ok | 42 | 42 | agree | kc_Elm02_96 |
| ClosureCapture03Test | err | -1 | -1 | agree | kc_Elm02_97 |
| ClosureCapture04Test | both | 30 | 30 | agree | kc_Elm02_98 |
| ClosureCapture04Test | first | 10 | 10 | agree | kc_Elm02_99 |
| ClosureCapture04Test | neither | 0 | 0 | agree | kc_Elm02_100 |
| ClosureCapture05Test | both | "ab" | "ab" | agree | kc_Elm02_101 |
| ClosureCapture05Test | one | "a" | "a" | agree | kc_Elm02_102 |
| ClosureCapture05Test | none | "" | "" | agree | kc_Elm02_103 |
| ClosureCapture06Test | both | "ab" | "ab" | agree | kc_Elm02_104 |
| ClosureCapture06Test | one | "a" | "a" | agree | kc_Elm02_105 |
| ClosureCapture06Test | none | "" | "" | agree | kc_Elm02_106 |
| ClosureCaptureBoolTest | when_true | 1 | 1 | agree | kc_Elm02_107 |
| ClosureCaptureBoolTest | when_false | 0 | 0 | agree | kc_Elm02_108 |
| ClosureCaptureRecordTest | rec | 6 | 6 | agree | kc_Elm02_109 |
| ClosureCaptureRecordTest | tup | 6 | 6 | agree | kc_Elm02_110 |
| ClosureCaptureTupleTest | add | 6 | 6 | agree | kc_Elm02_111 |
| ClosureCaptureTupleTest | nested | 10 | 10 | agree | kc_Elm02_112 |
| ClosureCaptureTupleTest | mixed | 9 | 9 | agree | kc_Elm02_113 |
| ClosureDifferentClosuresPerIfBranchInsideACaseTest | testValue | 20 | 20 | agree | kc_Elm02_114 |
| CombinatorBComposeTest | result | 25 | 25 | agree | kc_Elm02_115 |
| CombinatorBSumMapTest | result | 9 | 9 | agree | kc_Elm02_116 |
| CombinatorCConsTest | result | [1,2,3] | [1,2,3] | agree |  |
| CombinatorCFlipTest | result | -7 | -7 | agree | kc_Elm02_117 |

Elm02: 40 programs, 123 checks, 123 agree.

## Elm03

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| CombinatorIIdentityTest | result | 42 | 42 | agree | kc_Elm03_0 |
| CombinatorListStringTest | b_sum_map | 9 | 9 | agree | kc_Elm03_1 |
| CombinatorListStringTest | sp_mul | 84 | 84 | agree | kc_Elm03_2 |
| CombinatorListStringTest | w_concat | "hihi" | "hihi" | agree | kc_Elm03_3 |
| CombinatorListStringTest | c_cons | [1,2,3] | [1,2,3] | agree |  |
| CombinatorListStringTest | s_palindrome | "strawstraw!" | "strawstraw!" | agree | kc_Elm03_4 |
| CombinatorListStringTest | t_pipe | 12 | 12 | agree | kc_Elm03_5 |
| CombinatorListStringTest | p_lengths | 5 | 5 | agree | kc_Elm03_6 |
| CombinatorPLengthsTest | result | 5 | 5 | agree | kc_Elm03_7 |
| CombinatorRefIdentityBugTest | b_compose | 25 | 25 | agree | kc_Elm03_8 |
| CombinatorRefIdentityBugTest | s_feed | 15 | 15 | agree | kc_Elm03_9 |
| CombinatorSFeedTest | result | 15 | 15 | agree | kc_Elm03_10 |
| CombinatorSPalindromeTest | result | "strawstraw!" | "strawstraw!" | agree | kc_Elm03_11 |
| CombinatorSpCombineTest | result | 84 | 84 | agree | kc_Elm03_12 |
| CombinatorSpMulTest | result | 84 | 84 | agree | kc_Elm03_13 |
| CombinatorStdlibTCombinatorPipeListIntoComposedOpsTest | testValue | 12 | 12 | agree | kc_Elm03_14 |
| CombinatorTPipeTest | result | 12 | 12 | agree | kc_Elm03_15 |
| CombinatorTThrushTest | result | 21 | 21 | agree | kc_Elm03_16 |
| CombinatorTest | b_compose | 25 | 25 | agree | kc_Elm03_17 |
| CombinatorTest | c_flip | -7 | -7 | agree | kc_Elm03_18 |
| CombinatorTest | s_feed | 15 | 15 | agree | kc_Elm03_19 |
| CombinatorTest | sp_combine | 84 | 84 | agree | kc_Elm03_20 |
| CombinatorTest | w_dup | 81 | 81 | agree | kc_Elm03_21 |
| CombinatorTest | t_thrush | 21 | 21 | agree | kc_Elm03_22 |
| CombinatorTest | i_identity | 42 | 42 | agree | kc_Elm03_23 |
| CombinatorWConcatTest | result | "hihi" | "hihi" | agree | kc_Elm03_24 |
| CombinatorWDupTest | result | 81 | 81 | agree | kc_Elm03_25 |
| CompilerIssue1766LetMutualRecursionMismatchTest | result | Goal | Goal | agree | kc_Elm03_26 |
| CompilerIssue1793ComparableTupleLetCrashTest | f 1 | True | True | agree | kc_Elm03_27 |
| CompilerIssue1813TcoClosureCapturesMutatedArgTest | results | [1,2,3] | [1,2,3] | agree |  |
| CompilerIssue1858AnnotatedPolymorphicRecursionTest | bVals | Just "b" | Just "b" | agree |  |
| CompilerIssue1890RecordUpdateMutualRecursionCrashTest | result | { x = (), y = () } | { x = (), y = () } | agree |  |
| CompilerIssue1916PhantomExtensibleAliasCrashTest | bug | () | () | agree |  |
| CompilerIssue1964AnnotatedPolymorphicRecursionWrapperTest | depth | 2 | 2 | agree | kc_Elm03_28 |
| CompilerIssue2017TcoContinuationShadowedTest | windDown | 1 | 1 | agree | kc_Elm03_29 |
| CompilerIssue2057CallSiteChangesInferredTypeTest | sort | [] | [] | agree |  |
| CompilerIssue2221TcoContinuationTest | g 5 | 120 | 120 | agree | kc_Elm03_30 |
| CompilerIssue2252IdentityAliasTest | map | 3 | 3 | agree | kc_Elm03_31 |
| CompilerIssue2268TcoClosureCaptureTest | plain | [3,2,1] | [3,2,1] | agree |  |
| CompilerIssue2268TcoClosureCaptureTest | tco | [3,2,1] | [3,2,1] | agree |  |
| CompilerIssue2298IdentityAliasResultTest | make | 7 | 7 | agree | kc_Elm03_32 |
| CoreIssue988NanContainerSelfEqualityTest | record | False | False | agree | kc_Elm03_33 |
| CoreIssue988NanContainerSelfEqualityTest | custom type | False | False | agree | kc_Elm03_34 |
| CoreIssue988NanContainerSelfEqualityTest | maybe | False | False | agree | kc_Elm03_35 |
| CoreIssue988NanContainerSelfEqualityTest | shared inner tuple | False | False | agree | kc_Elm03_36 |
| CoreIssue988NanContainerSelfEqualityTest | shared inner list | False | False | agree | kc_Elm03_37 |
| CovLambdaBoundaryCaseBoundaryInARecursiveValueTest | testValue | 4 | 4 | agree | kc_Elm03_38 |
| CovLambdaBoundaryCaseBoundaryUnderAFunctionAliasTest | testValue | 4 | 4 | agree | kc_Elm03_39 |
| CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest | testValue | 9 | 9 | agree | kc_Elm03_40 |
| CovLambdaSetFunctionsInRecordsTuplesAndMaybeTest | testValue | 14 | 14 | agree | kc_Elm03_41 |
| CovPatternSplitTupleAndConstructorParametersMatchedByCaseTest | testValue | <function> | <function> | agree |  |
| CovTailRecPairParameterPassedUnchangedLetBoundAndRebuiltTest | testValue | <function> | <function> | agree |  |
| CovTailRecPairParametersSwappedAndALoopReturningALambdaTest | testValue | <function> | <function> | agree |  |
| CovTailRecSplitATripleParameterTest | testValue | <function> | <function> | agree |  |
| CustomTypeFuncFieldTest | op1 | 11 | 11 | agree | kc_Elm03_42 |
| CustomTypeFuncFieldTest | op2 | 20 | 20 | agree | kc_Elm03_43 |
| CustomTypePatternTest | name | "Alice" | "Alice" | agree | kc_Elm03_44 |
| CustomTypePatternTest | age | 30 | 30 | agree | kc_Elm03_45 |
| DecisionTreeAdvancedDeepNestingWithFallbackTest | testValue | 5 | 5 | agree | kc_Elm03_46 |
| DeepEqualityTest | nat 150 vs 200 | "False" | "False" | agree | kc_Elm03_47 |
| DeepEqualityTest | nat 150 vs 150 | "True" | "True" | agree | kc_Elm03_48 |
| DeepEqualityTest | nest 120 | "False" | "False" | agree | kc_Elm03_49 |
| DeepEqualityTest | nest 500 /= | "True" | "True" | agree | kc_Elm03_50 |
| DeepEqualityTest | record chain 300 | "False" | "False" | agree | kc_Elm03_51 |

Elm03: 40 programs, 64 checks, 64 agree.

## Elm04

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| DeepNestStressTest | nested_list | 1 | 1 | agree | kc_Elm04_0 |
| DeepNestStressTest | nested_tuple | 1 | 1 | agree | kc_Elm04_1 |
| DeepNestStressTest | nested_record | 1 | 1 | agree | kc_Elm04_2 |
| DeepNestStressTest | nested_let | 10 | 10 | agree | kc_Elm04_3 |
| DestructCaptureTest | captured | 56 | 56 | agree | kc_Elm04_4 |
| EdgeCaseAllDestructPatternsTest | testValue | [1,3,4,6] | [1,3,4,6] | agree |  |
| EitherTypeTest | left | 42 | 42 | agree | kc_Elm04_5 |
| EitherTypeTest | right | 0 | 0 | agree | kc_Elm04_6 |
| EitherTypeTest | mapLeft | 84 | 84 | agree | kc_Elm04_7 |
| EitherTypeTest | isLeft | True | True | agree | kc_Elm04_8 |
| EmbeddedEmptyStringCaptureTest | isEmpty | True | True | agree | kc_Elm04_9 |
| EmbeddedEmptyStringCaptureTest | captured | "" | "" | agree | kc_Elm04_10 |
| EmbeddedMixedConstantsTest | m | Nothing | Nothing | agree | kc_Elm04_11 |
| EmbeddedMixedConstantsTest | l | [] | [] | agree |  |
| EmbeddedMixedConstantsTest | b | True | True | agree | kc_Elm04_12 |
| EmbeddedMixedConstantsTest | s | "" | "" | agree | kc_Elm04_13 |
| EmbeddedMixedConstantsTest | u | () | () | agree |  |
| EmbeddedNilCaptureTest | result | "empty" | "empty" | agree | kc_Elm04_14 |
| EmbeddedNilInCustomTypeTest | isEmpty | True | True | agree | kc_Elm04_15 |
| EmbeddedNilInCustomTypeTest | len | 0 | 0 | agree | kc_Elm04_16 |
| EmbeddedNilRecursiveTest | result | [2,4,6] | [2,4,6] | agree |  |
| EmbeddedNothingCallbackTest | applied1 | Nothing | Nothing | agree | kc_Elm04_17 |
| EmbeddedNothingCallbackTest | applied2 | Just 11 | Just 11 | agree |  |
| EmbeddedNothingCaptureTest | result | -1 | -1 | agree | kc_Elm04_18 |
| EmbeddedNothingInCustomTypeTest | result | -1 | -1 | agree | kc_Elm04_19 |
| EmbeddedNothingInRecordTest | result | "nothing" | "nothing" | agree | kc_Elm04_20 |
| EmbeddedNothingInTupleTest | first | "nothing" | "nothing" | agree | kc_Elm04_21 |
| EmbeddedNothingInTupleTest | second | 42 | 42 | agree | kc_Elm04_22 |
| EmbeddedNothingMapTest | results | [-1,1,-1,2] | [-1,1,-1,2] | agree |  |
| EmbeddedNothingPolymorphicTest | r1 | Nothing | Nothing | agree | kc_Elm04_23 |
| EmbeddedNothingPolymorphicTest | r2 | [] | [] | agree |  |
| EmbeddedNothingPolymorphicTest | r3 | "" | "" | agree | kc_Elm04_24 |
| EmbeddedNothingRecursiveTest | find1 | Just 3 | Just 3 | agree |  |
| EmbeddedNothingRecursiveTest | find2 | Nothing | Nothing | agree | kc_Elm04_25 |
| EmbeddedReturnNilTest | r1 | [2,4] | [2,4] | agree |  |
| EmbeddedReturnNilTest | r2 | [] | [] | agree |  |
| EmbeddedReturnNothingTest | r1 | 5 | 5 | agree | kc_Elm04_26 |
| EmbeddedReturnNothingTest | r2 | -1 | -1 | agree | kc_Elm04_27 |
| EmbeddedUnitCaptureTest | first | () | () | agree |  |
| EmbeddedUnitCaptureTest | second | 42 | 42 | agree | kc_Elm04_28 |
| EqualityStringChainCaseTest | case1 | "matched foo+True" | "matched foo+True" | agree | kc_Elm04_29 |
| EqualityStringChainCaseTest | case2 | "matched bar+False" | "matched bar+False" | agree | kc_Elm04_30 |
| EqualityStringChainCaseTest | case3 | "other" | "other" | agree | kc_Elm04_31 |
| EqualityStringChainCaseTest | eq1 | True | True | agree | kc_Elm04_32 |
| EqualityStringChainCaseTest | eq2 | False | False | agree | kc_Elm04_33 |
| ErasedListSpecializationTest | n | 2 | 2 | agree | kc_Elm04_34 |
| ErasedListSpecializationTest | m | 3 | 3 | agree | kc_Elm04_35 |
| EscapeCustomCaseScrutineeTest | just | 7 | 7 | agree | kc_Elm04_36 |
| EscapeCustomCaseScrutineeTest | nothing | 0 | 0 | agree | kc_Elm04_37 |
| EscapeTopLevelTupleTest | a | 11 | 11 | agree | kc_Elm04_38 |
| EscapeTopLevelTupleTest | b | 22 | 22 | agree | kc_Elm04_39 |
| EtaExpandStateFunctionSequenceTest | testValue | 0 | 0 | agree | kc_Elm04_40 |
| EtaExpandStateTest | r | [30,42,54] | [30,42,54] | agree |  |
| File | compiled | True | True | agree | kc_Elm04_41 |
| FlipFunctionTest | result | 3.14 | 3.14 | agree |  |
| FloatEdgeTest | round 2.5 | "3" | "3" | agree |  |
| FloatEdgeTest | round -2.5 | "-2" | "-2" | agree |  |
| FloatEdgeTest | round 0.5 | "1" | "1" | agree |  |
| FloatEdgeTest | round -0.5 | "0" | "0" | agree |  |
| FloatEdgeTest | round 1.5 | "2" | "2" | agree |  |
| FloatEdgeTest | round -1.5 | "-1" | "-1" | agree |  |
| FloatEdgeTest | nan == nan | "False" | "False" | agree |  |
| FloatEdgeTest | nan /= nan | "True" | "True" | agree |  |
| FloatEdgeTest | 1 /= nan | "True" | "True" | agree |  |
| FloatEdgeTest | min 1 nan | "NaN" | "NaN" | agree |  |
| FloatEdgeTest | compare nan 1 | "GT" | "GT" | agree |  |
| FloatEdgeTest | foldl min | "NaN" | "NaN" | agree |  |
| FloatEdgeTest | map round | "[-2,0,3]" | "[-2,0,3]" | agree |  |
| FloatEdgeTest | case compare nan 1 | "GT" | "GT" | agree |  |
| FloatEdgeTest | case compare 1 2 | "LT" | "LT" | agree |  |
| FloatEdgeTest | case compare 2 2 | "EQ" | "EQ" | agree |  |
| FloatEdgeTest | compare tuple nan | "GT" | "GT" | agree |  |
| FloatEdgeTest | compare list nan | "GT" | "GT" | agree |  |
| FloatEdgeTest | just nan == just nan | "False" | "False" | agree |  |
| FloatEdgeTest | list nan /= list nan | "True" | "True" | agree |  |
| FloatEdgeTest | truncate nan | "0" | "0" | agree |  |
| FloatEdgeTest | pow 3 33 | "5559060566555523" | "5559060566555523" | agree |  |
| FunctionAccumulatorFunctionLookupTest | testValue | 15 | 15 | agree | kc_Elm04_42 |
| FunctionBasicTest | add1 | 5 | 5 | agree | kc_Elm04_43 |
| FunctionBasicTest | double1 | 10 | 10 | agree | kc_Elm04_44 |
| FunctionBasicTest | identity1 | 42 | 42 | agree | kc_Elm04_45 |
| FunctionChainedPartialApplicationTest | testValue | <function> | <function> | agree |  |
| FunctionCompappendWithStringTest | testValue | "helloworld" | "helloworld" | agree | kc_Elm04_46 |
| FunctionMultiArgTest | three | 6 | 6 | agree | kc_Elm04_47 |
| FunctionMultiArgTest | four | 10 | 10 | agree | kc_Elm04_48 |
| FunctionMultiArgTest | five | 15 | 15 | agree | kc_Elm04_49 |
| FunctionUnannotatedCompappendTest | testValue | 0 | 0 | agree | kc_Elm04_50 |
| FunctionValueChoiceTest | chooseIf called | 12 | 12 | agree | kc_Elm04_51 |
| FunctionValueChoiceTest | chooseIf folded | 6 | 6 | agree | kc_Elm04_52 |
| FunctionValueChoiceTest | chooseElse called | -1 | -1 | agree | kc_Elm04_53 |
| FunctionValueChoiceTest | chooseElse folded | 2 | 2 | agree | kc_Elm04_54 |
| FunctionValueChoiceTest | chooseC then | 7 | 7 | agree | kc_Elm04_55 |
| FunctionValueChoiceTest | chooseC else | (4,3) | (4,3) | agree |  |
| FunctionValueChoiceTest | chooseC sum | 17 | 17 | agree | kc_Elm04_56 |
| HOParamApplyTwoTest | result | 1 | 1 | agree | kc_Elm04_57 |
| HeteroClosureIntFloatTest | hetero_true | 13 | 13 | agree |  |
| HeteroClosureIntFloatTest | hetero_false | 10 | 10 | agree |  |
| HigherOrderFilterLikeFunctionTest | testValue | [1] | [1] | agree |  |
| HigherOrderFunctionChosenByIfTest | testValue | 2 | 2 | agree | kc_Elm04_58 |

Elm04: 40 programs, 99 checks, 99 agree.

## Elm05

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| HigherOrderFunctionFactoryTest | testValue | (5,2) | (5,2) | agree |  |
| HigherOrderReturnLambdaBasedOnConditionTest | testValue | 42 | 42 | agree | kc_Elm05_0 |
| HigherOrderTest | apply1 | 10 | 10 | agree | kc_Elm05_1 |
| HigherOrderTest | apply2 | 25 | 25 | agree | kc_Elm05_2 |
| HigherOrderTest | twice1 | 20 | 20 | agree | kc_Elm05_3 |
| HigherOrderTripleNestedFunctionTest | testValue | [1,2,3] | [1,2,3] | agree |  |
| HoleyAliasTwoParamsTest | pairInt | 42 | 42 | agree | kc_Elm05_4 |
| HoleyAliasTwoParamsTest | pairStr | "hi" | "hi" | agree | kc_Elm05_5 |
| HoleyAliasTwoParamsTest | recFloat | 2.5 | 2.5 | agree |  |
| HoleyAliasTwoParamsTest | recInt | 7 | 7 | agree | kc_Elm05_6 |
| HoleyAliasTwoParamsTest | box | Box (42,"hi") | Box (42,"hi") | agree |  |
| HoleyAliasTwoParamsTest | rbox | RBox { first = 7, second = 2.5 } | RBox { first = 7, second = 2.5 } | agree |  |
| ImportOperatorItemTest | sum | 7 | 7 | agree | kc_Elm05_7 |
| ImportOperatorItemTest | quotient | 3 | 3 | agree | kc_Elm05_8 |
| ImportResolutionQualifiedImportedFunctionTest | testValue | [-1,-2] | [-1,-2] | agree |  |
| IndirectCallFloatTest | apply_double | 10 | 10 | agree |  |
| IndirectCallFloatTest | apply_negate | -3 | -3 | agree |  |
| IndirectCallFloatTest | apply_addTen | 15 | 15 | agree |  |
| IndirectCallFloatTest | twice_double | 8 | 8 | agree |  |
| IndirectCallFloatTest | twice_addTen | 20 | 20 | agree |  |
| IndirectCallFloatTest | compose_result | 22 | 22 | agree |  |
| InfixAssocLeftArithTest | sub sub | 5 | 5 | agree | kc_Elm05_9 |
| InfixAssocLeftArithTest | fdiv fdiv | 5 | 5 | agree |  |
| InfixAssocLeftArithTest | idiv idiv | 3 | 3 | agree | kc_Elm05_10 |
| InfixAssocPipesTest | pipe right twice | 3 | 3 | agree | kc_Elm05_11 |
| InfixAssocPipesTest | pipe left twice | -3 | -3 | agree | kc_Elm05_12 |
| InfixAssocRightPowTest | pow pow | 512 | 512 | agree | kc_Elm05_13 |
| InfixIfExtendsRightTest | if then chain | 10 | 10 | agree | kc_Elm05_14 |
| InfixLastOperandAnyExprTest | if last | 3 | 3 | agree | kc_Elm05_15 |
| InfixLastOperandAnyExprTest | lambda last | 10 | 10 | agree | kc_Elm05_16 |
| InfixNegatedOperandTest | negated pow | 4 | 4 | agree | kc_Elm05_17 |
| InfixNegatedOperandTest | sub negated | 5 | 5 | agree | kc_Elm05_18 |
| InfixNonAssocSeparatedLegalTest | separated | True | True | agree | kc_Elm05_19 |
| InfixPrecAddOverConsTest | add then cons | [2,5] | [2,5] | agree |  |
| InfixPrecAndOverOrTest | or then and | True | True | agree | kc_Elm05_20 |
| InfixPrecAppendOverEqTest | append then eq | True | True | agree | kc_Elm05_21 |
| InfixPrecApplicationFirstTest | application then pow | 4 | 4 | agree | kc_Elm05_22 |
| InfixPrecApplicationFirstTest | application then mul | 9 | 9 | agree | kc_Elm05_23 |
| InfixPrecCompareOverAndTest | lt then and | True | True | agree | kc_Elm05_24 |
| InfixPrecComposeOverPipeTest | compose then pipe | -3 | -3 | agree | kc_Elm05_25 |
| InfixPrecMulOverAddTest | add then mul | 14 | 14 | agree | kc_Elm05_26 |
| InfixPrecMulOverAddTest | mul then add | 10 | 10 | agree | kc_Elm05_27 |
| InfixPrecOrOverPipeTest | or then pipe | False | False | agree | kc_Elm05_28 |
| InfixPrecPowOverMulTest | pow then mul | 16 | 16 | agree | kc_Elm05_29 |
| InlineDupLetNamesTest | InlineDupLetNamesTest | 6 | 6 | agree | kc_Elm05_30 |
| JoinpointABI23Majority3FlatTest | testValue | 10 | 10 | agree | kc_Elm05_31 |
| LambdaBoundaryCaptureTest | result | 105 | 105 | agree | kc_Elm05_32 |
| LambdaCaseBoundaryTest | add | 7 | 7 | agree | kc_Elm05_33 |
| LambdaCaseBoundaryTest | sub | 3 | 3 | agree | kc_Elm05_34 |
| LambdaCaseBoundaryTest | mul | 20 | 20 | agree | kc_Elm05_35 |
| LambdaCaseBoundaryTest | nested_add | 11 | 11 | agree | kc_Elm05_36 |
| LambdaCaseBoundaryTest | nested_sub | 3 | 3 | agree | kc_Elm05_37 |
| LambdaCaseBoundaryTest | partial_add | 15 | 15 | agree | kc_Elm05_38 |
| LambdaLetBoundaryTest | basic | 15 | 15 | agree | kc_Elm05_39 |
| LambdaLetBoundaryTest | capturing | 19 | 19 | agree | kc_Elm05_40 |
| LambdaLetBoundaryTest | multi_let | 20 | 20 | agree | kc_Elm05_41 |
| LambdaLetBoundaryTest | nested | 42 | 42 | agree | kc_Elm05_42 |
| LambdaLetBoundaryTest | partial | 25 | 25 | agree | kc_Elm05_43 |
| LambdaPatternArgTest | swap | (2,1) | (2,1) | agree |  |
| LambdaPatternArgTest | getX | 42 | 42 | agree | kc_Elm05_44 |
| LambdaPatternArgTest | mixed | "b" | "b" | agree | kc_Elm05_45 |
| LargeDispatchCaseTest | r1 | 3 | 3 | agree | kc_Elm05_46 |
| LargeDispatchCaseTest | r2 | -1 | -1 | agree | kc_Elm05_47 |
| LargeDispatchCaseTest | r3 | -5 | -5 | agree | kc_Elm05_48 |
| LargeDispatchCaseTest | r4 | 42 | 42 | agree | kc_Elm05_49 |
| LetBasicTest | result1 | 5 | 5 | agree | kc_Elm05_50 |
| LetBasicTest | result2 | "hello world" | "hello world" | agree | kc_Elm05_51 |
| LetBoundLambdaCallTest | result | 1 | 1 | agree | kc_Elm05_52 |
| LetDestructAliasTest | pair | (1,2) | (1,2) | agree |  |
| LetDestructAliasTest | first | 1 | 1 | agree | kc_Elm05_53 |
| LetDestructFuncTupleTest | get | 10 | 10 | agree | kc_Elm05_54 |
| LetDestructFuncTupleTest | set | 99 | 99 | agree | kc_Elm05_55 |
| LetDestructNestedSingleConstructorNumberTest | testValue | 1.5 | 1.5 | agree |  |
| LetDestructRecordTest | single | 42 | 42 | agree | kc_Elm05_56 |
| LetDestructRecordTest | multi | 3 | 3 | agree | kc_Elm05_57 |
| LetDestructRecordTest | partial | 4 | 4 | agree | kc_Elm05_58 |
| LetDestructRecordTest | mixed | 3 | 3 | agree | kc_Elm05_59 |
| LetDestructTupleNestedTest | basic | 3 | 3 | agree | kc_Elm05_60 |
| LetDestructTupleNestedTest | nested | 8 | 8 | agree | kc_Elm05_61 |
| LetDestructTupleNestedTest | chain | 6 | 6 | agree | kc_Elm05_62 |
| LetDestructuringTest | first | 1 | 1 | agree | kc_Elm05_63 |
| LetDestructuringTest | second | 2 | 2 | agree | kc_Elm05_64 |
| LetDestructuringTest | head | 10 | 10 | agree | kc_Elm05_65 |
| LetMultiFuncTest | r1 | 1 | 1 | agree | kc_Elm05_66 |
| LetMultiFuncTest | r2 | 2 | 2 | agree | kc_Elm05_67 |

Elm05: 40 programs, 85 checks, 85 agree.

## Elm06

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| LetMultipleTest | sum | 15 | 15 | agree | kc_Elm06_0 |
| LetMultipleTest | product | 120 | 120 | agree | kc_Elm06_1 |
| LetMutualRecursionBetweenLocalsTest | testValue | 22 | 22 | agree | kc_Elm06_2 |
| LetNestedTest | nested | 30 | 30 | agree | kc_Elm06_3 |
| LetNumberApplyToTest | applyTo | 45 | 45 | agree |  |
| LetNumberCaseLetTest | caselet | 45 | 45 | agree |  |
| LetNumberCaseTuple3Test | case-tuple3-int | 60 | 60 | agree |  |
| LetNumberCaseTuple3Test | case-tuple3-float | 61 | 61 | agree |  |
| LetNumberClosureInRecordTest | closrec | 45 | 45 | agree |  |
| LetNumberCustomTriple3Test | tri3 | 180 | 180 | agree |  |
| LetNumberCustomTypeTest | ctor | 45 | 45 | agree |  |
| LetNumberDeepNestRecordTest | deeprec | 45 | 45 | agree |  |
| LetNumberDestructureTest | destructure | 105 | 105 | agree |  |
| LetNumberFloatArithCrashTest | sqrt | 12 | 12 | agree |  |
| LetNumberFloatArithCrashTest | add | 31 | 31 | agree |  |
| LetNumberFloatArithCrashTest | div | 6 | 6 | agree |  |
| LetNumberFloatArithCrashTest | pow | 8 | 8 | agree |  |
| LetNumberFracRecordTest | frac | 34 | 34 | agree |  |
| LetNumberIfBranchTest | ifbr | 45 | 45 | agree |  |
| LetNumberIndirectCaptureTest | capture | 75 | 75 | agree |  |
| LetNumberIndirectDualTest | dual | (31,45) | (31,45) | agree |  |
| LetNumberIndirectIdentityTest | identity | 45 | 45 | agree |  |
| LetNumberIndirectTopFnTest | topfn | 45 | 45 | agree |  |
| LetNumberLetInLambdaTest | lamlet | 45 | 45 | agree |  |
| LetNumberListCaseTest | list-case-int | 2 | 2 | agree |  |
| LetNumberListCaseTest | list-case-float | 3 | 3 | agree |  |
| LetNumberListConsHeadTest | listcons | 45 | 45 | agree |  |
| LetNumberListFixedTest | listfixed | 105 | 105 | agree |  |
| LetNumberMaybeCaseDirectTest | maybedirect | 45 | 45 | agree |  |
| LetNumberMixedTupleSlotTest | mixedslot | 105 | 105 | agree |  |
| LetNumberMulFnTest | mulFn | 45 | 45 | agree |  |
| LetNumberNegateTest | neg | 12 | 12 | agree |  |
| LetNumberNestedCustomTest | nestcustom | 45 | 45 | agree |  |
| LetNumberNestedLetTest | nestedlet | 45 | 45 | agree |  |
| LetNumberNestedTupleTest | nesttup | 155 | 155 | agree |  |
| LetNumberRecordMultiFieldTest | multi | 105 | 105 | agree |  |
| LetNumberRecordToFnTest | rec2fn | 45 | 45 | agree |  |
| LetNumberScaleFnTest | scale | 105 | 105 | agree |  |
| LetNumberTupleRecordNestTest | tuprec | 105 | 105 | agree |  |
| LetNumberTupleToFnTest | tup2fn | 105 | 105 | agree |  |
| LetNumberUnionBranchTest | union | 145 | 145 | agree |  |
| LetNumberWildcardSlotTest | wildslot | 120 | 120 | agree |  |
| LetRecClosureTest | LetRecClosureTest | [1,2,3] | [1,2,3] | agree |  |
| LetRecMultiArgTest | result | 2 | 2 | agree | kc_Elm06_4 |
| ListConsCharTest | list | ['a','b','c'] | ['a','b','c'] | agree |  |
| ListConsCharTest | head | Just 'a' | Just 'a' | agree |  |
| ListConsCharTest | prepend | ['z','a','b','c'] | ['z','a','b','c'] | agree |  |
| ListConsFloatTest | list | [1,2.5,3.75] | [1,2.5,3.75] | agree |  |
| ListConsFloatTest | head | Just 1 | Just 1 | agree |  |
| ListConsFloatTest | prepend | [0,1,2.5,3.75] | [0,1,2.5,3.75] | agree |  |

Elm06: 40 programs, 50 checks, 50 agree.

## Elm07

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| ListConsIntTest | list | [1,2,3] | [1,2,3] | agree |  |
| ListConsIntTest | head | Just 1 | Just 1 | agree |  |
| ListConsIntTest | prepend | [0,1,2,3] | [0,1,2,3] | agree |  |
| ListConsTest | cons1 | [1] | [1] | agree |  |
| ListConsTest | cons2 | [1,2] | [1,2] | agree |  |
| ListConsTest | cons3 | [1,2,3] | [1,2,3] | agree |  |
| ListIndexedMapTest | testValue | [] | [] | agree |  |
| ListLiteralTest | list1 | [1] | [1] | agree |  |
| ListLiteralTest | list2 | [1,2,3] | [1,2,3] | agree |  |
| ListLiteralTest | list3 | [10,20,30,40,50] | [10,20,30,40,50] | agree |  |
| LocalMultiNonTailRecTest | sumInt | 6 | 6 | agree | kc_Elm07_0 |
| LocalMultiNonTailRecTest | sumFloat | 4 | 4 | agree |  |
| LocalRecCaptureBoolTest | count_true | 3 | 3 | agree | kc_Elm07_1 |
| LocalRecCaptureBoolTest | count_false | 4 | 4 | agree | kc_Elm07_2 |
| LocalRecCaptureKindsTest | direct | 110 | 110 | agree |  |
| LocalRecCaptureKindsTest | via_hof | [110,110] | [110,110] | agree |  |
| LocalRecCaptureSplitParamTest | o2 | 9 | 9 | agree | kc_Elm07_3 |
| LocalRecCaptureSplitParamTest | o3 | 9 | 9 | agree | kc_Elm07_4 |
| LocalTailRecSimpleTest | result | 55 | 55 | agree | kc_Elm07_5 |
| LssGapBodyTieAnnoAB | bodyTieAnn | 7 | 7 | agree | kc_Elm07_6 |
| LssGapBodyTieAnnoAB | bodyTieInf | 7 | 7 | agree | kc_Elm07_7 |
| LssGapCtorAsValue | ctorAsValue | 7 | 7 | agree | kc_Elm07_8 |
| LssGapCtorInList | ctorInList | 7 | 7 | agree | kc_Elm07_9 |
| LssGapCtorScale | ctorScale | 10 | 10 | agree | kc_Elm07_10 |
| LssGapCustomTypeFn | customTypeFn | 14 | 14 | agree | kc_Elm07_11 |
| LssGapNoDecls | noDecls | 14 | 14 | agree | kc_Elm07_12 |
| LssGapRecordFnNoAlias | recordFnNoAlias | 14 | 14 | agree | kc_Elm07_13 |
| LssGapTupleFn | tupleFn | 14 | 14 | agree | kc_Elm07_14 |
| MaybeJustTest | just1 | Just 42 | Just 42 | agree |  |
| MaybeJustTest | just2 | Just "hello" | Just "hello" | agree |  |
| MaybeJustTest | just3 | Just True | Just True | agree |  |
| MaybeNothingTest | nothing | Nothing | Nothing | agree | kc_Elm07_15 |
| MaybePatternMatchTest | match1 | 42 | 42 | agree | kc_Elm07_16 |
| MaybePatternMatchTest | match2 | 0 | 0 | agree | kc_Elm07_17 |
| MultiLocalTailRecTest | result | 15 | 15 | agree | kc_Elm07_18 |
| MutualLetRecClosuresTest | evenResult | True | True | agree | kc_Elm07_19 |
| MutualLetRecClosuresTest | oddResult | False | False | agree | kc_Elm07_20 |
| MutualLetRecClosuresTest | callsEven | 4 | 4 | agree | kc_Elm07_21 |
| MutualLetRecClosuresTest | callsOdd | 3 | 3 | agree | kc_Elm07_22 |
| MutualLetRecManyCapturesTest | go 3 | 42 | 42 | agree | kc_Elm07_23 |
| MutualLetRecManyCapturesTest | go 2 | 42 | 42 | agree | kc_Elm07_24 |
| MutualLetRecManyCapturesTest | go 1 | 42 | 42 | agree | kc_Elm07_25 |
| MutualLetRecManyCapturesTest | go 0 | 42 | 42 | agree | kc_Elm07_26 |
| MutualLetRecNestedTest | run 3 | 42 | 42 | agree | kc_Elm07_27 |
| MutualLetRecNestedTest | run 2 | 84 | 84 | agree | kc_Elm07_28 |
| MutualLetRecNestedTest | run 1 | 42 | 42 | agree | kc_Elm07_29 |
| MutualLetRecNestedTest | run 0 | 84 | 84 | agree | kc_Elm07_30 |
| MutualRecursionTest | isEven0 | True | True | agree | kc_Elm07_31 |
| MutualRecursionTest | isEven5 | False | False | agree | kc_Elm07_32 |
| MutualRecursionTest | isOdd5 | True | True | agree | kc_Elm07_33 |
| MutualRecursionThreeWayTest | a10 | 1 | 1 | agree | kc_Elm07_34 |
| MutualRecursionThreeWayTest | a9 | 0 | 0 | agree | kc_Elm07_35 |
| MutualRecursionThreeWayTest | a3 | 0 | 0 | agree | kc_Elm07_36 |
| MutualRecursionThreeWayTest | a0 | 0 | 0 | agree | kc_Elm07_37 |
| NestedCaseReturnTest | r1 | "integer" | "integer" | agree | kc_Elm07_38 |
| NestedCaseReturnTest | r2 | "text" | "text" | agree | kc_Elm07_39 |
| NestedCaseReturnTest | r3 | "custom List" | "custom List" | agree | kc_Elm07_40 |
| NestedCaseReturnTest | r4 | "other" | "other" | agree | kc_Elm07_41 |
| NestedCaseReturnTest | r5 | "empty" | "empty" | agree | kc_Elm07_42 |
| NonAsciiIdentifierTest | NonAsciiIdentifierTest | 7 | 7 | agree | kc_Elm07_43 |
| NonZeroArityRecursionTest | countDown | 0 | 0 | agree | kc_Elm07_44 |
| NumberDestructFieldTest | tuple field | 2.5 | 2.5 | agree |  |
| NumberDestructFieldTest | list field | 1.25 | 1.25 | agree |  |
| NumberDestructFieldTest | record field | 4.5 | 4.5 | agree |  |
| NumberDestructFieldTest | maybe field | 5.5 | 5.5 | agree |  |
| NumberDestructFieldTest | nested | (3.5,4) | (3.5,4) | agree |  |
| NumberGenericAppCustom | numgenapp | 45 | 45 | agree |  |
| PapEtaCtorProbe | final | { depth = 9, stats = { a = 2, b = 2, shape = 4 } } | { depth = 9, stats = { a = 2, b = 2, shape = 4 } } | agree |  |
| ParenthesesTest | grouped | 9 | 9 | agree | kc_Elm07_45 |
| ParenthesesTest | ungrouped | 7 | 7 | agree | kc_Elm07_46 |
| ParenthesesTest | redundant | 5 | 5 | agree | kc_Elm07_47 |
| ParenthesesTest | nested pattern | [3,0,-1] | [3,0,-1] | agree |  |
| ParenthesesTest | parenthesised types | [2,4] | [2,4] | agree |  |
| PartialAppCaptureTypesTest | float_cap | 1.5 | 1.5 | agree |  |
| PartialAppCaptureTypesTest | char_cap | 'x' | 'x' | agree |  |
| PartialAppCaptureTypesTest | bool_cap | True | True | agree | kc_Elm07_48 |
| PartialAppCaptureTypesTest | string_cap | "hello" | "hello" | agree | kc_Elm07_49 |
| PartialAppCaptureTypesTest | combined | 3.5 | 3.5 | agree |  |
| PartialAppChainTest | chain1 | 10 | 10 | agree | kc_Elm07_50 |
| PartialAppChainTest | chain2 | 6 | 6 | agree | kc_Elm07_51 |
| PartialApplicationTest | partial1 | 7 | 7 | agree | kc_Elm07_52 |
| PartialApplicationTest | partial2 | 15 | 15 | agree | kc_Elm07_53 |
| PartialApplicationTest | partial3 | [2,3,4] | [2,3,4] | agree |  |
| PhantomTypeVarTest | result | 42 | 42 | agree | kc_Elm07_54 |
| PolyApplyLambdaTest | applyIntId | 1 | 1 | agree | kc_Elm07_55 |
| PolyApplyLambdaTest | applyStrId | "hi" | "hi" | agree | kc_Elm07_56 |
| PolyApplyLambdaTest | applyLambda | 42 | 42 | agree | kc_Elm07_57 |
| PolyChainCallTest | size | 2 | 2 | agree | kc_Elm07_58 |
| PolyChainDictLikeInsertChained5TimesWithTupleKeysConcreteCallerTest | testValue | 1 | 1 | agree | kc_Elm07_59 |

Elm07: 40 programs, 89 checks, 89 agree.

## Elm08

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| PolyChainFoldlLikeCalled8TimesOverTupleKeyedStructureTest | testValue | 0 | 0 | agree | kc_Elm08_0 |
| PolyEscapePolymorphicFunctionExtractedFromTupleTest | testValue | 42 | 42 | agree | kc_Elm08_1 |
| PolyEscapeRecordTest | result | 42 | 42 | agree | kc_Elm08_2 |
| PolyEscapeRecordTest | narrowed | 6 | 6 | agree | kc_Elm08_3 |
| PolyLetConstTest | r1 | 1 | 1 | agree | kc_Elm08_4 |
| PolyLetConstTest | r2 | "hi" | "hi" | agree | kc_Elm08_5 |
| PolyLetTailRecTwoTypesTest | r | (6,2) | (6,2) | agree |  |
| PolySpecializeRecursiveTest | intLen | 3 | 3 | agree | kc_Elm08_6 |
| PolySpecializeRecursiveTest | strLen | 2 | 2 | agree | kc_Elm08_7 |
| PolySpecializeRecursiveTest | intMap | [2,4,6] | [2,4,6] | agree |  |
| PolySpecializeRecursiveTest | strMap | ["aa","bb"] | ["aa","bb"] | agree |  |
| PolyStepLoopFloatResultTest | result | 3.14 | 3.14 | agree |  |
| PolyStepLoopFloatResultTest | state | 6 | 6 | agree | kc_Elm08_8 |
| PolyStepLoopFoldMIntTest | sum | 15 | 15 | agree | kc_Elm08_9 |
| PolyStepLoopFoldMIntTest | final | 104 | 104 | agree | kc_Elm08_10 |
| PolyTailRecReverseTest | intRev | [3,2,1] | [3,2,1] | agree |  |
| PolyTailRecReverseTest | strRev | ["c","b","a"] | ["c","b","a"] | agree |  |
| RecordAccessTest | x | 1 | 1 | agree | kc_Elm08_11 |
| RecordAccessTest | y | 2 | 2 | agree | kc_Elm08_12 |
| RecordAccessTest | name | "Alice" | "Alice" | agree | kc_Elm08_13 |
| RecordAccessorFunctionCaseTest | testValue | 1 | 1 | agree | kc_Elm08_14 |
| RecordAccessorFunctionTest | names | ["Alice","Bob"] | ["Alice","Bob"] | agree |  |
| RecordAccessorFunctionTest | xs | [1,4] | [1,4] | agree |  |
| RecordChainedUpdateTest | multi | { x = 100, y = 20, z = 300 } | { x = 100, y = 20, z = 300 } | agree |  |
| RecordChainedUpdateTest | chain | { x = 10, y = 20 } | { x = 10, y = 20 } | agree |  |
| RecordChainedUpdatesTest | testValue | { x = 10, y = 20 } | { x = 10, y = 20 } | agree |  |
| RecordCreateTest | record1 | { x = 1, y = 2 } | { x = 1, y = 2 } | agree |  |
| RecordCreateTest | record2 | { age = 30, name = "Alice" } | { age = 30, name = "Alice" } | agree |  |
| RecordNestedAccessTest | deep | 42 | 42 | agree | kc_Elm08_15 |
| RecordNestedAccessTest | chain | 99 | 99 | agree | kc_Elm08_16 |
| RecordUpdatePolyFieldTest | f | 6 | 6 | agree | kc_Elm08_17 |
| RecordUpdatePolyFieldTest | g | 0 | 0 | agree | kc_Elm08_18 |
| RecordUpdateTest | updated | { x = 10, y = 2 } | { x = 10, y = 2 } | agree |  |
| RecordUpdateTest | original | { x = 1, y = 2 } | { x = 1, y = 2 } | agree |  |
| RecordWithFunctionsTest | apply1 | 11 | 11 | agree | kc_Elm08_19 |
| RecordWithFunctionsTest | apply2 | 20 | 20 | agree | kc_Elm08_20 |
| RecordWithFunctionsTest | composed | 22 | 22 | agree | kc_Elm08_21 |
| RecordWithFunctionsTest | updated | 7 | 7 | agree | kc_Elm08_22 |
| RecursiveFactorialTest | fact0 | 1 | 1 | agree | kc_Elm08_23 |
| RecursiveFactorialTest | fact5 | 120 | 120 | agree | kc_Elm08_24 |
| RecursiveFactorialTest | fact10 | 3628800 | 3628800 | agree | kc_Elm08_25 |
| RecursiveFibonacciTest | fib0 | 0 | 0 | agree | kc_Elm08_26 |
| RecursiveFibonacciTest | fib1 | 1 | 1 | agree | kc_Elm08_27 |
| RecursiveFibonacciTest | fib10 | 55 | 55 | agree | kc_Elm08_28 |
| RecursiveListLengthTest | len0 | 0 | 0 | agree | kc_Elm08_29 |
| RecursiveListLengthTest | len3 | 3 | 3 | agree | kc_Elm08_30 |
| RecursiveListLengthTest | len5 | 5 | 5 | agree | kc_Elm08_31 |
| RecursiveMutualTypeTest | nodes | 4 | 4 | agree | kc_Elm08_32 |
| RecursiveTopLevelLambdaTest | testValue | 4 | 4 | agree | kc_Elm08_33 |
| RecursiveTreeTest | sum | 6 | 6 | agree | kc_Elm08_34 |
| RecursiveTreeTest | depth | 3 | 3 | agree | kc_Elm08_35 |
| RecursiveTypeInRecordTest | eval | 6 | 6 | agree | kc_Elm08_36 |
| RowVariableAloneTest | x | 1 | 1 | agree | kc_Elm08_37 |
| RowVariableAloneTest | rest z | "b" | "b" | agree | kc_Elm08_38 |
| SingleCtorPairBoolCharTest | match_true | "yes" | "yes" | agree | kc_Elm08_39 |
| SingleCtorPairBoolCharTest | match_false | "no" | "no" | agree | kc_Elm08_40 |
| SingleCtorPairBoolCharTest | unwrap_char | 'x' | 'x' | agree |  |
| SingleCtorPairBoolFloatTest | match_true | "yes" | "yes" | agree | kc_Elm08_41 |
| SingleCtorPairBoolFloatTest | match_false | "no" | "no" | agree | kc_Elm08_42 |
| SingleCtorPairBoolFloatTest | unwrap_float | 3.14 | 3.14 | agree |  |
| SingleCtorPairBoolIntBidiTest | match_true | "yes" | "yes" | agree | kc_Elm08_43 |
| SingleCtorPairBoolIntBidiTest | match_false | "no" | "no" | agree | kc_Elm08_44 |
| SingleCtorPairBoolIntBidiTest | match_pos | "positive" | "positive" | agree | kc_Elm08_45 |
| SingleCtorPairBoolIntBidiTest | match_neg | "non-positive" | "non-positive" | agree | kc_Elm08_46 |
| SingleCtorPairBoolIntBidiTest | extract_bool | True | True | agree | kc_Elm08_47 |
| SingleCtorPairBoolIntBidiTest | extract_int | 42 | 42 | agree | kc_Elm08_48 |
| SingleCtorPairCharFloatTest | unwrap_char | 'Z' | 'Z' | agree |  |
| SingleCtorPairCharFloatTest | unwrap_float | 1.5 | 1.5 | agree |  |
| SingleCtorPairCharFloatTest | match_char | ("got",'Z') | ("got",'Z') | agree |  |
| SingleCtorPairCharIntTest | unwrap_char | 'A' | 'A' | agree |  |
| SingleCtorPairCharIntTest | unwrap_int | 256 | 256 | agree | kc_Elm08_49 |
| SingleCtorPairCharIntTest | match_char | ("got",'A') | ("got",'A') | agree |  |
| SingleCtorPairFloatBoolTest | unwrap_float | 9.81 | 9.81 | agree |  |
| SingleCtorPairFloatBoolTest | match_true | "yes" | "yes" | agree | kc_Elm08_50 |
| SingleCtorPairFloatBoolTest | match_false | "no" | "no" | agree | kc_Elm08_51 |
| SingleCtorPairFloatBoolTest | match_float | "big" | "big" | agree | kc_Elm08_52 |
| SingleCtorPairIntFloatTest | unwrap_int | 42 | 42 | agree | kc_Elm08_53 |
| SingleCtorPairIntFloatTest | unwrap_float | 2.718 | 2.718 | agree |  |
| SingleCtorPairIntFloatTest | match_int_pos | "positive" | "positive" | agree | kc_Elm08_54 |
| SingleCtorPairIntFloatTest | match_float_big | "big" | "big" | agree | kc_Elm08_55 |
| SingleCtorPairStringBoolTest | unwrap_str | "world" | "world" | agree | kc_Elm08_56 |
| SingleCtorPairStringBoolTest | match_true | "yes" | "yes" | agree | kc_Elm08_57 |
| SingleCtorPairStringBoolTest | match_false | "no" | "no" | agree | kc_Elm08_58 |
| SingleCtorPairStringIntTest | unwrap_str | "hello" | "hello" | agree | kc_Elm08_59 |
| SingleCtorPairStringIntTest | unwrap_int | 99 | 99 | agree | kc_Elm08_60 |
| SingleCtorPairStringIntTest | match_str | "found_hello" | "found_hello" | agree | kc_Elm08_61 |
| SingleCtorPairUnitIntTest | unwrap_unit | () | () | agree |  |
| SingleCtorPairUnitIntTest | unwrap_int | 77 | 77 | agree | kc_Elm08_62 |
| SingleCtorPairUnitIntTest | match_unit | "got_unit" | "got_unit" | agree | kc_Elm08_63 |
| StandardA93MutualNumberDefaultTest | f 3 | 0 | 0 | agree | kc_Elm08_64 |
| StandardApplicationStrictTest | before | () | () | agree |  |
| StandardApplicationStrictTest | app strict | (no value) | (no value) | agree |  |
| StandardCoreEvaluationExamplesTest | as-pattern | (1,[1,2]) | (1,[1,2]) | agree |  |
| StandardCoreEvaluationExamplesTest | unit pattern | 5 | 5 | agree | kc_Elm08_65 |
| StandardCoreEvaluationExamplesTest | operator value | 3 | 3 | agree | kc_Elm08_66 |
| StandardCoreEvaluationExamplesTest | partial basic value | <function> | <function> | agree |  |
| StandardCoreEvaluationExamplesTest | partial constructor | <function> | <function> | agree |  |
| StandardCoreEvaluationExamplesTest | (&&) is strict | False | False | agree | kc_Elm08_67 |
| StandardCoreEvaluationExamplesTest | pipe | 6 | 6 | agree | kc_Elm08_68 |
| StandardCoreEvaluationExamplesTest | mrule-fail | 2 | 2 | agree | kc_Elm08_69 |
| StandardCoreEvaluationExamplesTest | Just 1 | Just 1 | Just 1 | agree |  |
| StandardCoreEvaluationExamplesTest | inc 0.5 | 1.5 | 1.5 | agree |  |
| StandardCoreEvaluationExamplesTest | modBy 4 -5 | 3 | 3 | agree | kc_Elm08_70 |
| StandardCoreEvaluationExamplesTest | remainderBy 4 -5 | -1 | -1 | agree | kc_Elm08_71 |
| StandardCoreEvaluationExamplesTest | record field order | True | True | agree | kc_Elm08_72 |
| StandardCoreEvaluationExamplesTest | compare strings | LT | LT | agree | kc_Elm08_73 |
| StandardCoreEvaluationExamplesTest | accessor | 7 | 7 | agree | kc_Elm08_74 |

Elm08: 40 programs, 107 checks, 107 agree.

## Elm09

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| StandardLetStrictTest | before | () | () | agree |  |
| StandardLetStrictTest | let strict | (no value) | (no value) | agree |  |
| StringCasePatternCommaTest | one_comma | "comma" | "comma" | agree | kc_Elm09_0 |
| StringCasePatternCommaTest | one_a | "other" | "other" | agree | kc_Elm09_1 |
| StringCasePatternCommaTest | two_a | "a" | "a" | agree | kc_Elm09_2 |
| StringCasePatternCommaTest | two_b | "b" | "b" | agree | kc_Elm09_3 |
| StringCasePatternCommaTest | two_comma | "other" | "other" | agree | kc_Elm09_4 |
| StringCreationMatrixTest | Creation.eq | True | True | agree | kc_Elm09_5 |
| StringCreationMatrixTest | Creation.case | True | True | agree | kc_Elm09_6 |
| StringEscapeCrTest | cr | True | True | agree | kc_Elm09_7 |
| StringEscapeCrTest | mixed | True | True | agree | kc_Elm09_8 |
| StringEscapeCrTest | crlf | True | True | agree | kc_Elm09_9 |
| StringEscapeCrTest | triple | True | True | agree | kc_Elm09_10 |
| StringEscapeCrTest | pattern | "carriage return" | "carriage return" | agree | kc_Elm09_11 |
| StringLiteralTest | str1 | "Hello" | "Hello" | agree | kc_Elm09_12 |
| StringLiteralTest | str2 | "Hello, World!" | "Hello, World!" | agree | kc_Elm09_13 |
| StringLiteralTest | str3 | "abc123" | "abc123" | agree | kc_Elm09_14 |
| StringMagicPrefixTest | s1 | "__mlir_unknown_loc__" | "__mlir_unknown_loc__" | agree | kc_Elm09_15 |
| StringMagicPrefixTest | s2 | "__mlir_loc__:foo:1:2" | "__mlir_loc__:foo:1:2" | agree | kc_Elm09_16 |
| StringMagicPrefixTest | s3 | "__mlir_loc__:" | "__mlir_loc__:" | agree | kc_Elm09_17 |
| StringMagicPrefixTest | s4 | "loc:unknown" | "loc:unknown" | agree | kc_Elm09_18 |
| TailLoopMutualRecMutualRecursionInsideATailLoopTest | testValue | 2 | 2 | agree | kc_Elm09_19 |
| TailRecBoolCarryTest | result1 | 10 | 10 | agree | kc_Elm09_20 |
| TailRecBoolCarryTest | result2 | 0 | 0 | agree | kc_Elm09_21 |
| TailRecBoolCarryTest | result3 | 42 | 42 | agree | kc_Elm09_22 |
| TailRecCaseDestructTest | foldl | 15 | 15 | agree | kc_Elm09_23 |
| TailRecCaseDestructTest | sum | 10 | 10 | agree | kc_Elm09_24 |
| TailRecCaseDestructTest | count | 3 | 3 | agree | kc_Elm09_25 |
| TailRecCaseMultiBranchTypesTest | result | FoundLE 2 | FoundLE 2 | agree |  |
| TailRecClosureAccTest | result | 15 | 15 | agree | kc_Elm09_26 |
| TailRecCustomCaseTest | total | 10 | 10 | agree | kc_Elm09_27 |
| TailRecDeciderSearchTest | found | 42 | 42 | agree | kc_Elm09_28 |
| TailRecDecoderLoopTest | r1 | "decode_int" | "decode_int" | agree | kc_Elm09_29 |
| TailRecDecoderLoopTest | r2 | "decode_string" | "decode_string" | agree | kc_Elm09_30 |
| TailRecDecoderLoopTest | r3 | "decode_list(decode_int)" | "decode_list(decode_int)" | agree | kc_Elm09_31 |
| TailRecDecoderLoopTest | r4 | "decode_custom(Foo)" | "decode_custom(Foo)" | agree | kc_Elm09_32 |
| TailRecFoldlCaseTest | result | 6 | 6 | agree | kc_Elm09_33 |
| TailRecManyBranchStringTest | result | "found-beta" | "found-beta" | agree | kc_Elm09_34 |
| TailRecMultiCaseWhileTest | total | 8 | 8 | agree | kc_Elm09_35 |
| TailRecMultiCaseWhileTest | special | 2 | 2 | agree | kc_Elm09_36 |
| TailRecNestedCaseTest | find | True | True | agree | kc_Elm09_37 |
| TailRecNestedCaseTest | nofind | False | False | agree | kc_Elm09_38 |
| TailRecNestedCaseTest | last | 4 | 4 | agree | kc_Elm09_39 |
| TailRecNestedStringCaseTest | result | 42 | 42 | agree | kc_Elm09_40 |
| TailRecTypeTraversalTest | result | "integer" | "integer" | agree | kc_Elm09_41 |
| TailRecursiveSumTest | sum1 | 15 | 15 | agree | kc_Elm09_42 |
| TailRecursiveSumTest | sum2 | 55 | 55 | agree | kc_Elm09_43 |
| TailRecursiveSumTest | sum3 | 5050 | 5050 | agree | kc_Elm09_44 |
| TopLevelNameReplacesImportTest | own max | 3 | 3 | agree | kc_Elm09_45 |
| TopLevelNameReplacesImportTest | Basics.max | 2 | 2 | agree | kc_Elm09_46 |
| TupleCharFieldTest | pair | ('A',65) | ('A',65) | agree |  |
| TuplePairTest | pair1 | (1,2) | (1,2) | agree |  |
| TuplePairTest | pair2 | ("a","b") | ("a","b") | agree |  |
| TuplePairTest | pair3 | (True,False) | (True,False) | agree |  |
| TupleTripleTest | triple1 | (1,2,3) | (1,2,3) | agree |  |
| TupleTripleTest | triple2 | ("a","b","c") | ("a","b","c") | agree |  |
| TypeClassConstraintTest | absInt | 5 | 5 | agree | kc_Elm09_47 |
| TypeClassConstraintTest | absFloat | 3.14 | 3.14 | agree |  |
| TypeClassConstraintTest | minInt | 3 | 3 | agree | kc_Elm09_48 |
| TypeClassConstraintTest | concatStr | "hello world" | "hello world" | agree | kc_Elm09_49 |
| UnreachableModuleTest | ran | True | True | agree | kc_Elm09_50 |
| UserBoolNamedCtorTest | pickTrue | 1 | 1 | agree | kc_Elm09_51 |
| UserBoolNamedCtorTest | pickFalse | 2 | 2 | agree | kc_Elm09_52 |
| UserBoolNamedCtorTest | pickUnknown | 3 | 3 | agree | kc_Elm09_53 |
| UserBoolNamedCtorTest | names | ["T","F","U"] | ["T","F","U"] | agree |  |
| WideClosureSat26Test | res | [6208,6215] | [6208,6215] | agree |  |
| WideCtorField24Test | field23 | 1023 | 1023 | agree | kc_Elm09_54 |
| WideCtorField24Test | field24 | 1024 | 1024 | agree | kc_Elm09_55 |
| WideCtorField24Test | field25 | 2.5 | 2.5 | agree |  |
| WideCtorField24Test | field26 | 'z' | 'z' | agree |  |
| WideCtorField24Test | sum24 | 2048 | 2048 | agree | kc_Elm09_56 |
| WideCtorMixedTest | field23 | "23s" | "23s" | agree | kc_Elm09_57 |
| WideCtorMixedTest | field24 | True | True | agree | kc_Elm09_58 |
| WideCtorMixedTest | field55 | 1055 | 1055 | agree | kc_Elm09_59 |
| WideCtorMixedTest | field59 | False | False | agree | kc_Elm09_60 |
| WideCtorMixedTest | eq self | True | True | agree | kc_Elm09_61 |
| WideCtorMixedTest | eq other | False | False | agree | kc_Elm09_62 |
| WideCtorMixedTest | show | W 1000 1.5 'c' "3s" True 1005 6.5 'h' "8s" False 1010 11.5 'm' "13s" True 1015 16.5 'r' "18s" False 1020 21.5 'w' "23s" True 1025 26.5 'b' "28s" False 1030 31.5 'g' "33s" True 1035 36.5 'l' "38s" False 1040 41.5 'q' "43s" True 1045 46.5 'v' "48s" False 1050 51.5 'a' "53s" True 1055 56.5 'f' "58s" False | W 1000 1.5 'c' "3s" True 1005 6.5 'h' "8s" False 1010 11.5 'm' "13s" True 1015 16.5 'r' "18s" False 1020 21.5 'w' "23s" True 1025 26.5 'b' "28s" False 1030 31.5 'g' "33s" True 1035 36.5 'l' "38s" False 1040 41.5 'q' "43s" True 1045 46.5 'v' "48s" False 1050 51.5 'a' "53s" True 1055 56.5 'f' "58s" False | agree |  |
| WideRecord33Test | f0000 | 1000 | 1000 | agree | kc_Elm09_63 |
| WideRecord33Test | f0031 | 31.5 | 31.5 | agree |  |
| WideRecord33Test | f0032 | 'g' | 'g' | agree |  |
| WideRecord33Test | pattern | (1000,'g') | (1000,'g') | agree |  |
| WideRecord33Test | update | '!' | '!' | agree |  |
| WideRecord33Test | eq self | True | True | agree | kc_Elm09_64 |
| WideRecord33Test | eq updated | False | False | agree | kc_Elm09_65 |
| WideRecord33Test | show | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g' } | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g' } | agree |  |
| WideRecord40Test | f0000 | 1000 | 1000 | agree | kc_Elm09_66 |
| WideRecord40Test | f0031 | 31.5 | 31.5 | agree |  |
| WideRecord40Test | f0032 | 'g' | 'g' | agree |  |
| WideRecord40Test | f0039 | False | False | agree | kc_Elm09_67 |
| WideRecord40Test | pattern | (1000,False) | (1000,False) | agree |  |
| WideRecord40Test | update | True | True | agree | kc_Elm09_68 |
| WideRecord40Test | eq self | True | True | agree | kc_Elm09_69 |
| WideRecord40Test | eq updated | False | False | agree | kc_Elm09_70 |
| WideRecord40Test | show | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g', f0033 = "33s", f0034 = True, f0035 = 1035, f0036 = 36.5, f0037 = 'l', f0038 = "38s", f0039 = False } | { f0000 = 1000, f0001 = 1.5, f0002 = 'c', f0003 = "3s", f0004 = True, f0005 = 1005, f0006 = 6.5, f0007 = 'h', f0008 = "8s", f0009 = False, f0010 = 1010, f0011 = 11.5, f0012 = 'm', f0013 = "13s", f0014 = True, f0015 = 1015, f0016 = 16.5, f0017 = 'r', f0018 = "18s", f0019 = False, f0020 = 1020, f0021 = 21.5, f0022 = 'w', f0023 = "23s", f0024 = True, f0025 = 1025, f0026 = 26.5, f0027 = 'b', f0028 = "28s", f0029 = False, f0030 = 1030, f0031 = 31.5, f0032 = 'g', f0033 = "33s", f0034 = True, f0035 = 1035, f0036 = 36.5, f0037 = 'l', f0038 = "38s", f0039 = False } | agree |  |
| WideRecordPatternTest | access f27 | 1027 | 1027 | agree | kc_Elm09_71 |
| WideRecordPatternTest | access f25 | 1025 | 1025 | agree | kc_Elm09_72 |
| WideRecordPatternTest | pattern | 1028025 | 1028025 | agree | kc_Elm09_73 |
| WideRecordPatternTest | update f27 | 1028 | 1028 | agree | kc_Elm09_74 |
| WideRecordPatternTest | update f26 | 7 | 7 | agree | kc_Elm09_75 |
| WideRecordPatternTest | update pattern | 1029025 | 1029025 | agree | kc_Elm09_76 |
| WrapperUnionFieldTest | result | 7 | 7 | agree | kc_Elm09_77 |

Elm09: 35 programs, 102 checks, 102 agree.

## ElmCore01

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| BasicsClampTest | clamp_low | 5 | 5 | agree | kc_ElmCore01_0 |
| BasicsClampTest | clamp_mid | 7 | 7 | agree | kc_ElmCore01_1 |
| BasicsClampTest | clamp_high | 10 | 10 | agree | kc_ElmCore01_2 |
| BasicsClampTest | clamp_float | 3.5 | 3.5 | agree |  |
| BasicsIdentityTest | identity_int | 42 | 42 | agree | kc_ElmCore01_3 |
| BasicsIdentityTest | identity_string | "hello" | "hello" | agree | kc_ElmCore01_4 |
| BasicsIdentityTest | always_result | 99 | 99 | agree | kc_ElmCore01_5 |
| BasicsIsNaNTest | nan_check | True | True | agree | kc_ElmCore01_6 |
| BasicsIsNaNTest | not_nan | False | False | agree | kc_ElmCore01_7 |
| BasicsIsNaNTest | inf_check | True | True | agree | kc_ElmCore01_8 |
| BasicsIsNaNTest | not_inf | False | False | agree | kc_ElmCore01_9 |
| BasicsModByTest | mod_pos | 1 | 1 | agree | kc_ElmCore01_10 |
| BasicsModByTest | mod_neg | 2 | 2 | agree | kc_ElmCore01_11 |
| BasicsModByTest | mod_zero | 0 | 0 | agree | kc_ElmCore01_12 |
| BoolNotTest | not1 | False | False | agree | kc_ElmCore01_13 |
| BoolNotTest | not2 | True | True | agree | kc_ElmCore01_14 |
| BoolXorTest | xor1 | False | False | agree | kc_ElmCore01_15 |
| BoolXorTest | xor2 | True | True | agree | kc_ElmCore01_16 |
| BoolXorTest | xor3 | True | True | agree | kc_ElmCore01_17 |
| BoolXorTest | xor4 | False | False | agree | kc_ElmCore01_18 |
| CeilingToIntTest | ceil1 | 3 | 3 | agree |  |
| CeilingToIntTest | ceil2 | -2 | -2 | agree |  |
| CharAstralCodeTest | bmp | 8364 | 8364 | agree | kc_ElmCore01_19 |
| CharAstralCodeTest | emoji | 128512 | 128512 | agree | kc_ElmCore01_20 |
| CharAstralCodeTest | clef | 119070 | 119070 | agree | kc_ElmCore01_21 |
| CharAstralCodeTest | maxcp | 1114111 | 1114111 | agree | kc_ElmCore01_22 |
| CharFromCodeTest | char1 | 'A' | 'A' | agree |  |
| CharFromCodeTest | char2 | 'a' | 'a' | agree |  |
| CharFromCodeTest | char3 | '0' | '0' | agree |  |
| CharToCodeTest | code1 | 65 | 65 | agree | kc_ElmCore01_23 |
| CharToCodeTest | code2 | 97 | 97 | agree | kc_ElmCore01_24 |
| CharToCodeTest | code3 | 48 | 48 | agree | kc_ElmCore01_25 |
| CharToCodeThroughFunctionTest | code | 65 | 65 | agree | kc_ElmCore01_26 |
| ComparableMinMaxTest | minStr | "apple" | "apple" | agree | kc_ElmCore01_27 |
| ComparableMinMaxTest | maxStr | "zebra" | "zebra" | agree | kc_ElmCore01_28 |
| ComparableMinMaxTest | minChar | 'a' | 'a' | agree |  |
| ComparableMinMaxTest | maxChar | 'z' | 'z' | agree |  |
| CompareCharCaptureTest | sorted | ['a','b','c','d','e'] | ['a','b','c','d','e'] | agree |  |
| CompareCharCaptureTest | reverse_sorted | ['e','d','c','b','a'] | ['e','d','c','b','a'] | agree |  |
| CompareCharTest | cmp1 | LT | LT | agree | kc_ElmCore01_29 |
| CompareCharTest | cmp2 | GT | GT | agree | kc_ElmCore01_30 |
| CompareCharTest | cmp3 | EQ | EQ | agree | kc_ElmCore01_31 |
| CompareCustomWithEmptyListFieldTest | cmp_ee | EQ | EQ | agree | kc_ElmCore01_32 |
| CompareCustomWithEmptyListFieldTest | cmp_eA | LT | LT | agree | kc_ElmCore01_33 |
| CompareCustomWithEmptyListFieldTest | cmp_Ae | GT | GT | agree | kc_ElmCore01_34 |
| CompareCustomWithEmptyListFieldTest | eq_ee | True | True | agree | kc_ElmCore01_35 |
| CompareCustomWithEmptyListFieldTest | eq_eA | False | False | agree | kc_ElmCore01_36 |
| CompareCustomWithEmptyListFieldTest | eq_Ae | False | False | agree | kc_ElmCore01_37 |
| CompareEmptyListTest | ee | EQ | EQ | agree | kc_ElmCore01_38 |
| CompareEmptyListTest | ea | LT | LT | agree | kc_ElmCore01_39 |
| CompareEmptyListTest | ae | GT | GT | agree | kc_ElmCore01_40 |
| CompareEmptyListTest | eab | LT | LT | agree | kc_ElmCore01_41 |
| CompareEmptyListTest | abe | GT | GT | agree | kc_ElmCore01_42 |
| CompareEmptyListTest | aa | EQ | EQ | agree | kc_ElmCore01_43 |
| CompareEmptyListTest | ab | LT | LT | agree | kc_ElmCore01_44 |
| CompareEmptyListTest | ba | GT | GT | agree | kc_ElmCore01_45 |
| CompareEmptyListTest | aba | GT | GT | agree | kc_ElmCore01_46 |
| CompareEmptyStringTest | ee | EQ | EQ | agree | kc_ElmCore01_47 |
| CompareEmptyStringTest | ea | LT | LT | agree | kc_ElmCore01_48 |
| CompareEmptyStringTest | ae | GT | GT | agree | kc_ElmCore01_49 |
| CompareEmptyStringTest | eab | LT | LT | agree | kc_ElmCore01_50 |
| CompareEmptyStringTest | abe | GT | GT | agree | kc_ElmCore01_51 |
| CompareEmptyStringTest | aa | EQ | EQ | agree | kc_ElmCore01_52 |
| CompareEmptyStringTest | ab | LT | LT | agree | kc_ElmCore01_53 |
| CompareEmptyStringTest | ba | GT | GT | agree | kc_ElmCore01_54 |
| CompareEmptyStringTest | aba | GT | GT | agree | kc_ElmCore01_55 |
| CompareFloatCaptureTest | sorted | [1.5,2,2.75,3,4.25] | [1.5,2,2.75,3,4.25] | agree |  |
| CompareFloatCaptureTest | reverse_sorted | [4.25,3,2.75,2,1.5] | [4.25,3,2.75,2,1.5] | agree |  |
| CompareFloatTest | cmp1 | LT | LT | agree | kc_ElmCore01_56 |
| CompareFloatTest | cmp2 | GT | GT | agree | kc_ElmCore01_57 |
| CompareFloatTest | cmp3 | EQ | EQ | agree | kc_ElmCore01_58 |
| CompareIntCaptureTest | sorted | [1,2,3,4,5] | [1,2,3,4,5] | agree |  |
| CompareIntCaptureTest | reverse_sorted | [5,4,3,2,1] | [5,4,3,2,1] | agree |  |
| CompareIntTest | cmp1 | LT | LT | agree | kc_ElmCore01_59 |
| CompareIntTest | cmp2 | GT | GT | agree | kc_ElmCore01_60 |
| CompareIntTest | cmp3 | EQ | EQ | agree | kc_ElmCore01_61 |
| CompareNestedEmptyListTest | ee | EQ | EQ | agree | kc_ElmCore01_62 |
| CompareNestedEmptyListTest | eA | LT | LT | agree | kc_ElmCore01_63 |
| CompareNestedEmptyListTest | Ae | GT | GT | agree | kc_ElmCore01_64 |
| CompareNestedEmptyListTest | midEmpty | LT | LT | agree | kc_ElmCore01_65 |
| CompareNestedEmptyListTest | midNonEmpty | GT | GT | agree | kc_ElmCore01_66 |
| CompareRecordWithEmptyListFieldTest | cmp_ee | EQ | EQ | agree | kc_ElmCore01_67 |
| CompareRecordWithEmptyListFieldTest | cmp_eA | LT | LT | agree | kc_ElmCore01_68 |
| CompareRecordWithEmptyListFieldTest | cmp_Ae | GT | GT | agree | kc_ElmCore01_69 |
| CompareRecordWithEmptyListFieldTest | eq_ee | True | True | agree | kc_ElmCore01_70 |
| CompareRecordWithEmptyListFieldTest | eq_eA | False | False | agree | kc_ElmCore01_71 |
| CompareRecordWithEmptyListFieldTest | eq_Ae | False | False | agree | kc_ElmCore01_72 |
| CompareStringTest | cmp1 | LT | LT | agree | kc_ElmCore01_73 |
| CompareStringTest | cmp2 | GT | GT | agree | kc_ElmCore01_74 |
| CompareStringTest | cmp3 | EQ | EQ | agree | kc_ElmCore01_75 |
| CompareTupleWithEmptyListNestedTest | ee | EQ | EQ | agree | kc_ElmCore01_76 |
| CompareTupleWithEmptyListNestedTest | eA | LT | LT | agree | kc_ElmCore01_77 |
| CompareTupleWithEmptyListNestedTest | Ae | GT | GT | agree | kc_ElmCore01_78 |
| CompareTupleWithEmptyListNestedTest | triple_eA | LT | LT | agree | kc_ElmCore01_79 |
| CompareTupleWithEmptyListNestedTest | triple_Ae | GT | GT | agree | kc_ElmCore01_80 |
| CompareTupleWithEmptyListTest | ee | EQ | EQ | agree | kc_ElmCore01_81 |
| CompareTupleWithEmptyListTest | eA | LT | LT | agree | kc_ElmCore01_82 |
| CompareTupleWithEmptyListTest | Ae | GT | GT | agree | kc_ElmCore01_83 |
| CompareTupleWithEmptyListTest | eAB | LT | LT | agree | kc_ElmCore01_84 |
| CompareTupleWithEmptyListTest | ABe | GT | GT | agree | kc_ElmCore01_85 |
| CompareTupleWithEmptyListTest | f0_ee | LT | LT | agree | kc_ElmCore01_86 |
| CompareTupleWithEmptyListTest | f0_Ae | GT | GT | agree | kc_ElmCore01_87 |
| CompareTupleWithEmptyStringTest | ee | EQ | EQ | agree | kc_ElmCore01_88 |
| CompareTupleWithEmptyStringTest | ea | LT | LT | agree | kc_ElmCore01_89 |
| CompareTupleWithEmptyStringTest | ae | GT | GT | agree | kc_ElmCore01_90 |
| CompareTupleWithEmptyStringTest | f0_ea | LT | LT | agree | kc_ElmCore01_91 |
| CompareTupleWithEmptyStringTest | f0_ae | GT | GT | agree | kc_ElmCore01_92 |
| CompilerIssue2362NanTupleEqualityTest | nan == nan | False | False | agree | kc_ElmCore01_93 |
| CompilerIssue2362NanTupleEqualityTest | p == q | False | False | agree | kc_ElmCore01_94 |
| CompilerIssue2362NanTupleEqualityTest | p == p | False | False | agree | kc_ElmCore01_95 |
| CompositionTest | compose1 | 20 | 20 | agree | kc_ElmCore01_96 |
| CompositionTest | compose2 | 11 | 11 | agree | kc_ElmCore01_97 |
| CompositionTest | pipe1 | 20 | 20 | agree | kc_ElmCore01_98 |
| ContainerCompareCharTest | pairLt | LT | LT | agree | kc_ElmCore01_99 |
| ContainerCompareCharTest | pairGt | GT | GT | agree | kc_ElmCore01_100 |
| ContainerCompareCharTest | pairEq | EQ | EQ | agree | kc_ElmCore01_101 |
| ContainerCompareCharTest | pairSecondDecides | LT | LT | agree | kc_ElmCore01_102 |
| ContainerCompareCharTest | pairUpperBeforeLower | LT | LT | agree | kc_ElmCore01_103 |
| ContainerCompareCharTest | pairUnicode | LT | LT | agree | kc_ElmCore01_104 |
| ContainerCompareCharTest | tripleFirstDecides | LT | LT | agree | kc_ElmCore01_105 |
| ContainerCompareCharTest | tripleThirdDecides | GT | GT | agree | kc_ElmCore01_106 |
| ContainerCompareCharTest | tripleEq | EQ | EQ | agree | kc_ElmCore01_107 |
| ContainerCompareCharTest | tripleDigitsBeforeLetters | LT | LT | agree | kc_ElmCore01_108 |
| ContainerCompareCharTest | listLt | LT | LT | agree | kc_ElmCore01_109 |
| ContainerCompareCharTest | listShorterIsLess | LT | LT | agree | kc_ElmCore01_110 |
| ContainerCompareCharTest | listEq | EQ | EQ | agree | kc_ElmCore01_111 |
| ContainerCompareCharTest | listEmptyIsLeast | LT | LT | agree | kc_ElmCore01_112 |
| ContainerCompareCharTest | listUnicodeCmp | LT | LT | agree | kc_ElmCore01_113 |
| ContainerCompareCharTest | pairLtOp | True | True | agree | kc_ElmCore01_114 |
| ContainerCompareCharTest | pairGeOp | True | True | agree | kc_ElmCore01_115 |
| ContainerCompareCharTest | tripleLtOp | True | True | agree | kc_ElmCore01_116 |
| ContainerCompareCharTest | listGtOp | True | True | agree | kc_ElmCore01_117 |
| ContainerEqualityCharTest | pairEqual | True | True | agree | kc_ElmCore01_118 |
| ContainerEqualityCharTest | pairFirstDiff | False | False | agree | kc_ElmCore01_119 |
| ContainerEqualityCharTest | pairSecondDiff | False | False | agree | kc_ElmCore01_120 |
| ContainerEqualityCharTest | pairCaseDiff | False | False | agree | kc_ElmCore01_121 |
| ContainerEqualityCharTest | pairDigits | True | True | agree | kc_ElmCore01_122 |
| ContainerEqualityCharTest | pairUnicode | True | True | agree | kc_ElmCore01_123 |
| ContainerEqualityCharTest | pairUnicodeDiff | False | False | agree | kc_ElmCore01_124 |
| ContainerEqualityCharTest | tripleEqual | True | True | agree | kc_ElmCore01_125 |
| ContainerEqualityCharTest | tripleMidDiff | False | False | agree | kc_ElmCore01_126 |
| ContainerEqualityCharTest | tripleMixedCase | True | True | agree | kc_ElmCore01_127 |
| ContainerEqualityCharTest | tripleUnicode | True | True | agree | kc_ElmCore01_128 |
| ContainerEqualityCharTest | listEqual | True | True | agree | kc_ElmCore01_129 |
| ContainerEqualityCharTest | listLenDiff | False | False | agree | kc_ElmCore01_130 |
| ContainerEqualityCharTest | listEmpty | True | True | agree | kc_ElmCore01_131 |
| ContainerEqualityCharTest | listCaseDiff | False | False | agree | kc_ElmCore01_132 |
| ContainerEqualityCharTest | listUnicode | True | True | agree | kc_ElmCore01_133 |
| ContainerEqualityCustomFloatTest | ptEqual | True | True | agree | kc_ElmCore01_134 |
| ContainerEqualityCustomFloatTest | ptXDiff | False | False | agree | kc_ElmCore01_135 |
| ContainerEqualityCustomFloatTest | ptYDiff | False | False | agree | kc_ElmCore01_136 |
| ContainerEqualityCustomFloatTest | ptNegZero | True | True | agree | kc_ElmCore01_137 |
| ContainerEqualityCustomFloatTest | ptNaNFirst | False | False | agree | kc_ElmCore01_138 |
| ContainerEqualityCustomFloatTest | ptNaNSecond | False | False | agree | kc_ElmCore01_139 |
| ContainerEqualityCustomFloatTest | ptPosInf | True | True | agree | kc_ElmCore01_140 |
| ContainerEqualityCustomFloatTest | ptInfSign | False | False | agree | kc_ElmCore01_141 |
| ContainerEqualityCustomFloatTest | triEqual | True | True | agree | kc_ElmCore01_142 |
| ContainerEqualityCustomFloatTest | triMidDiff | False | False | agree | kc_ElmCore01_143 |
| ContainerEqualityCustomFloatTest | triAllNegZero | True | True | agree | kc_ElmCore01_144 |
| ContainerEqualityCustomFloatTest | triNaNMid | False | False | agree | kc_ElmCore01_145 |
| ContainerEqualityCustomFloatTest | triMixedInf | True | True | agree | kc_ElmCore01_146 |
| ContainerEqualityCustomFloatTest | mixedCtorDiff | False | False | agree | kc_ElmCore01_147 |
| ContainerEqualityRecordFloatTest | recEqual | True | True | agree | kc_ElmCore01_148 |
| ContainerEqualityRecordFloatTest | recXDiff | False | False | agree | kc_ElmCore01_149 |
| ContainerEqualityRecordFloatTest | recYDiff | False | False | agree | kc_ElmCore01_150 |
| ContainerEqualityRecordFloatTest | recNegZero | True | True | agree | kc_ElmCore01_151 |
| ContainerEqualityRecordFloatTest | recNaN | False | False | agree | kc_ElmCore01_152 |
| ContainerEqualityRecordFloatTest | recPosInf | True | True | agree | kc_ElmCore01_153 |
| ContainerEqualityRecordFloatTest | recInfSign | False | False | agree | kc_ElmCore01_154 |
| ContainerEqualityRecordFloatTest | rec3Equal | True | True | agree | kc_ElmCore01_155 |
| ContainerEqualityRecordFloatTest | rec3MidDiff | False | False | agree | kc_ElmCore01_156 |
| ContainerEqualityRecordFloatTest | rec3AllNegZero | True | True | agree | kc_ElmCore01_157 |
| ContainerEqualityRecordFloatTest | rec3NaNMid | False | False | agree | kc_ElmCore01_158 |
| ContainerEqualityRecordFloatTest | rec3MixedInf | True | True | agree | kc_ElmCore01_159 |
| ContainerEqualityStringTest | pairEqual | True | True | agree | kc_ElmCore01_160 |
| ContainerEqualityStringTest | pairFirstDiff | False | False | agree | kc_ElmCore01_161 |
| ContainerEqualityStringTest | pairSecondDiff | False | False | agree | kc_ElmCore01_162 |
| ContainerEqualityStringTest | pairEmpty | True | True | agree | kc_ElmCore01_163 |
| ContainerEqualityStringTest | pairCaseDiff | False | False | agree | kc_ElmCore01_164 |
| ContainerEqualityStringTest | pairPrefixDiff | False | False | agree | kc_ElmCore01_165 |
| ContainerEqualityStringTest | pairUnicode | True | True | agree | kc_ElmCore01_166 |
| ContainerEqualityStringTest | tripleEqual | True | True | agree | kc_ElmCore01_167 |
| ContainerEqualityStringTest | tripleMidDiff | False | False | agree | kc_ElmCore01_168 |
| ContainerEqualityStringTest | tripleWithEmpty | True | True | agree | kc_ElmCore01_169 |
| ContainerEqualityStringTest | tripleUnicode | True | True | agree | kc_ElmCore01_170 |
| ContainerEqualityStringTest | listEqual | True | True | agree | kc_ElmCore01_171 |
| ContainerEqualityStringTest | listLenDiff | False | False | agree | kc_ElmCore01_172 |
| ContainerEqualityStringTest | listEmpty | True | True | agree | kc_ElmCore01_173 |
| ContainerEqualityStringTest | listEmptyStrings | True | True | agree | kc_ElmCore01_174 |
| ContainerEqualityStringTest | listCaseDiff | False | False | agree | kc_ElmCore01_175 |
| ContainerEqualityStringTest | listUnicode | True | True | agree | kc_ElmCore01_176 |
| ControlFlowBooleanWithNotTest | testValue | True | True | agree | kc_ElmCore01_177 |
| CoreIssue1050NanGreaterThanNanTest | nan > nan | False | False | agree | kc_ElmCore01_178 |
| CoreIssue1050NanGreaterThanNanTest | nan >= nan | False | False | agree | kc_ElmCore01_179 |
| CoreIssue1080ClampNanTest | clamp nan | NaN | NaN | agree |  |
| CoreIssue1115NanEqualsLiteralZeroTest | nan == 0 | False | False | agree | kc_ElmCore01_180 |
| CoreIssue1115NanEqualsLiteralZeroTest | 0 == nan | False | False | agree | kc_ElmCore01_181 |
| CoreIssue1115NanEqualsLiteralZeroTest | nan == zero | False | False | agree | kc_ElmCore01_182 |
| CoreIssue988NanEqualityReferenceTest | same answer | True | True | agree | kc_ElmCore01_183 |
| EqBoxedFastPathTest | strSame | True | True | agree | kc_ElmCore01_184 |
| EqBoxedFastPathTest | strTwin | True | True | agree | kc_ElmCore01_185 |
| EqBoxedFastPathTest | strDiff | False | False | agree | kc_ElmCore01_186 |
| EqBoxedFastPathTest | strNe | True | True | agree | kc_ElmCore01_187 |
| EqBoxedFastPathTest | listSame | True | True | agree | kc_ElmCore01_188 |
| EqBoxedFastPathTest | listTwin | True | True | agree | kc_ElmCore01_189 |
| EqBoxedFastPathTest | listDiff | False | False | agree | kc_ElmCore01_190 |
| EqBoxedFastPathTest | tupleTwin | True | True | agree | kc_ElmCore01_191 |
| EqBoxedFastPathTest | tupleDiff | False | False | agree | kc_ElmCore01_192 |
| EqBoxedFastPathTest | recordTwin | True | True | agree | kc_ElmCore01_193 |
| EqBoxedFastPathTest | recordDiff | False | False | agree | kc_ElmCore01_194 |
| EqBoxedFastPathTest | customTwin | True | True | agree | kc_ElmCore01_195 |
| EqBoxedFastPathTest | customDiff | False | False | agree | kc_ElmCore01_196 |
| EqBoxedFastPathTest | unitEq | True | True | agree | kc_ElmCore01_197 |
| EqBoxedFastPathTest | emptyStrEq | True | True | agree | kc_ElmCore01_198 |
| EqBoxedFastPathTest | emptyListEq | True | True | agree | kc_ElmCore01_199 |
| EqBoxedFastPathTest | boolTT | True | True | agree | kc_ElmCore01_200 |
| EqBoxedFastPathTest | boolTF | False | False | agree | kc_ElmCore01_201 |
| EqBoxedFastPathTest | boolNe | True | True | agree | kc_ElmCore01_202 |
| EqBoxedFastPathTest | nestedTwin | True | True | agree | kc_ElmCore01_203 |

ElmCore01: 40 programs, 219 checks, 219 agree.

## ElmCore02

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| EqualityBoolCaseTest | cTT | "yes" | "yes" | agree | kc_ElmCore02_0 |
| EqualityBoolCaseTest | cTF | "no" | "no" | agree | kc_ElmCore02_1 |
| EqualityBoolCaseTest | cFT | "no" | "no" | agree | kc_ElmCore02_2 |
| EqualityBoolCaseTest | cFF | "yes" | "yes" | agree | kc_ElmCore02_3 |
| EqualityBoolContainerTest | pairTT_TT | True | True | agree | kc_ElmCore02_4 |
| EqualityBoolContainerTest | pairTT_TF | False | False | agree | kc_ElmCore02_5 |
| EqualityBoolContainerTest | pairTF_TT | False | False | agree | kc_ElmCore02_6 |
| EqualityBoolContainerTest | pairTF_FT | False | False | agree | kc_ElmCore02_7 |
| EqualityBoolContainerTest | tripleTFT_TFT | True | True | agree | kc_ElmCore02_8 |
| EqualityBoolContainerTest | tripleTFT_TFF | False | False | agree | kc_ElmCore02_9 |
| EqualityBoolContainerTest | listTT_TT | True | True | agree | kc_ElmCore02_10 |
| EqualityBoolContainerTest | listTF_TF | True | True | agree | kc_ElmCore02_11 |
| EqualityBoolContainerTest | listTF_FT | False | False | agree | kc_ElmCore02_12 |
| EqualityBoolContainerTest | listTF_TT | False | False | agree | kc_ElmCore02_13 |
| EqualityBoolContainerTest | listEmpty | True | True | agree | kc_ElmCore02_14 |
| EqualityBoolIfTest | ifTT | "yes" | "yes" | agree | kc_ElmCore02_15 |
| EqualityBoolIfTest | ifTF | "no" | "no" | agree | kc_ElmCore02_16 |
| EqualityBoolIfTest | ifFT | "no" | "no" | agree | kc_ElmCore02_17 |
| EqualityBoolIfTest | ifFF | "yes" | "yes" | agree | kc_ElmCore02_18 |
| EqualityBoolIfTest | nifTT | "no" | "no" | agree | kc_ElmCore02_19 |
| EqualityBoolIfTest | nifTF | "yes" | "yes" | agree | kc_ElmCore02_20 |
| EqualityBoolMaybeTest | justTT | True | True | agree | kc_ElmCore02_21 |
| EqualityBoolMaybeTest | justTF | False | False | agree | kc_ElmCore02_22 |
| EqualityBoolMaybeTest | justFF | True | True | agree | kc_ElmCore02_23 |
| EqualityBoolMaybeTest | justFT | False | False | agree | kc_ElmCore02_24 |
| EqualityBoolMaybeTest | nothingNothing | True | True | agree | kc_ElmCore02_25 |
| EqualityBoolMaybeTest | justTrueNothing | False | False | agree | kc_ElmCore02_26 |
| EqualityBoolMaybeTest | nothingJustFalse | False | False | agree | kc_ElmCore02_27 |
| EqualityBoolPapTest | isTrueList | [True,False,True,False] | [True,False,True,False] | agree |  |
| EqualityBoolPapTest | isFalseList | [False,True,False,True] | [False,True,False,True] | agree |  |
| EqualityBoolPapTest | filterTrue | [True,True] | [True,True] | agree |  |
| EqualityBoolPapTest | filterFalse | [False,False] | [False,False] | agree |  |
| EqualityBoolPapTest | anyTrue | True | True | agree | kc_ElmCore02_28 |
| EqualityBoolPapTest | anyFalse | True | True | agree | kc_ElmCore02_29 |
| EqualityBoolRecordTest | recEq | True | True | agree | kc_ElmCore02_30 |
| EqualityBoolRecordTest | recDiffA | False | False | agree | kc_ElmCore02_31 |
| EqualityBoolRecordTest | recDiffB | False | False | agree | kc_ElmCore02_32 |
| EqualityBoolRecordTest | recDiffBoth | False | False | agree | kc_ElmCore02_33 |
| EqualityBoolRecordTest | recFF_FF | True | True | agree | kc_ElmCore02_34 |
| EqualityBoolTest | tt | True | True | agree | kc_ElmCore02_35 |
| EqualityBoolTest | tf | False | False | agree | kc_ElmCore02_36 |
| EqualityBoolTest | ft | False | False | agree | kc_ElmCore02_37 |
| EqualityBoolTest | ff | True | True | agree | kc_ElmCore02_38 |
| EqualityBoolTest | ntt | False | False | agree | kc_ElmCore02_39 |
| EqualityBoolTest | ntf | True | True | agree | kc_ElmCore02_40 |
| EqualityBoolTest | nft | True | True | agree | kc_ElmCore02_41 |
| EqualityBoolTest | nff | False | False | agree | kc_ElmCore02_42 |
| EqualityBoolVarTest | vTT | True | True | agree | kc_ElmCore02_43 |
| EqualityBoolVarTest | vTF | False | False | agree | kc_ElmCore02_44 |
| EqualityBoolVarTest | vFT | False | False | agree | kc_ElmCore02_45 |
| EqualityBoolVarTest | vFF | True | True | agree | kc_ElmCore02_46 |
| EqualityBoolVarTest | hTT | True | True | agree | kc_ElmCore02_47 |
| EqualityBoolVarTest | hTF | False | False | agree | kc_ElmCore02_48 |
| EqualityBoolVarTest | hFT | False | False | agree | kc_ElmCore02_49 |
| EqualityBoolVarTest | hFF | True | True | agree | kc_ElmCore02_50 |
| EqualityOtherConstantsTest | emptyEmpty | True | True | agree | kc_ElmCore02_51 |
| EqualityOtherConstantsTest | emptyNonEmpty | False | False | agree | kc_ElmCore02_52 |
| EqualityOtherConstantsTest | nonEmptyEmpty | False | False | agree | kc_ElmCore02_53 |
| EqualityOtherConstantsTest | nilNil | True | True | agree | kc_ElmCore02_54 |
| EqualityOtherConstantsTest | nilCons | False | False | agree | kc_ElmCore02_55 |
| EqualityOtherConstantsTest | consNil | False | False | agree | kc_ElmCore02_56 |
| EqualityOtherConstantsTest | nothingNothing | True | True | agree | kc_ElmCore02_57 |
| EqualityOtherConstantsTest | nothingJust | False | False | agree | kc_ElmCore02_58 |
| EqualityOtherConstantsTest | justNothing | False | False | agree | kc_ElmCore02_59 |
| EqualityOtherConstantsTest | unitUnit | True | True | agree | kc_ElmCore02_60 |
| EqualityTest | eq1 | True | True | agree | kc_ElmCore02_61 |
| EqualityTest | eq2 | False | False | agree | kc_ElmCore02_62 |
| EqualityTest | ne1 | True | True | agree | kc_ElmCore02_63 |
| EqualityTest | ne2 | False | False | agree | kc_ElmCore02_64 |
| EqualityTest | listEq | True | True | agree | kc_ElmCore02_65 |
| FloatAbsTest | abs1 | 3.14 | 3.14 | agree |  |
| FloatAbsTest | abs2 | 3.14 | 3.14 | agree |  |
| FloatAbsTest | abs3 | 0 | 0 | agree |  |
| FloatAddTest | add1 | 13 | 13 | agree |  |
| FloatAddTest | add2 | 0 | 0 | agree |  |
| FloatAddTest | add3 | -5 | -5 | agree |  |
| FloatCeilingTest | ceil1 | 3 | 3 | agree |  |
| FloatCeilingTest | ceil2 | 2 | 2 | agree |  |
| FloatCeilingTest | ceil3 | -2 | -2 | agree |  |
| FloatCeilingTest | ceil4 | -2 | -2 | agree |  |
| FloatCompareTest | lt | True | True | agree | kc_ElmCore02_66 |
| FloatCompareTest | gt | True | True | agree | kc_ElmCore02_67 |
| FloatCompareTest | le | True | True | agree | kc_ElmCore02_68 |
| FloatCompareTest | ge | True | True | agree | kc_ElmCore02_69 |
| FloatCompareTest | eq | True | True | agree | kc_ElmCore02_70 |
| FloatCompareTest | ne | True | True | agree | kc_ElmCore02_71 |
| FloatDivTest | div1 | 2.5 | 2.5 | agree |  |
| FloatDivTest | div2 | -2.5 | -2.5 | agree |  |
| FloatDivTest | div3 | -2.5 | -2.5 | agree |  |
| FloatDivTest | div4 | 2.5 | 2.5 | agree |  |
| FloatFloorTest | floor1 | 2 | 2 | agree |  |
| FloatFloorTest | floor2 | 2 | 2 | agree |  |
| FloatFloorTest | floor3 | -3 | -3 | agree |  |
| FloatFloorTest | floor4 | -3 | -3 | agree |  |
| FloatInfinityTest | isInf1 | True | True | agree | kc_ElmCore02_72 |
| FloatInfinityTest | isInf2 | True | True | agree | kc_ElmCore02_73 |
| FloatInfinityTest | isInf3 | False | False | agree | kc_ElmCore02_74 |
| FloatMathAcosTest | testValue | 0 | 0 | agree |  |
| FloatMathAsinTest | testValue | 0 | 0 | agree |  |
| FloatMathAtan2Test | testValue | 0.7853981633974483 | 0.7853981633974483 | agree |  |
| FloatMathAtanTest | testValue | 0 | 0 | agree |  |
| FloatMathBasicsETest | testValue | 2.718281828459045 | 2.718281828459045 | agree |  |
| FloatMathFloatLessThanTest | testValue | True | True | agree | kc_ElmCore02_75 |
| FloatMathIsNaNTest | testValue | True | True | agree | kc_ElmCore02_76 |
| FloatMathSin2PlusCos21Test | testValue | 1 | 1 | agree |  |
| FloatMathTanTest | testValue | 0 | 0 | agree |  |
| FloatMinMaxTest | min1 | 3.14 | 3.14 | agree |  |
| FloatMinMaxTest | min2 | -5 | -5 | agree |  |
| FloatMinMaxTest | max1 | 10 | 10 | agree |  |
| FloatMinMaxTest | max2 | 5 | 5 | agree |  |
| FloatMulTest | mul1 | 30 | 30 | agree |  |
| FloatMulTest | mul2 | -15 | -15 | agree |  |
| FloatMulTest | mul3 | 6 | 6 | agree |  |
| FloatMulTest | mul4 | 0 | 0 | agree |  |
| FloatNegateTest | neg1 | -3.14 | -3.14 | agree |  |
| FloatNegateTest | neg2 | 3.14 | 3.14 | agree |  |
| FloatNegateTest | neg3 | 0 | 0 | agree |  |
| FloatNegativeZeroTest | eq | True | True | agree | kc_ElmCore02_77 |
| FloatNegativeZeroTest | div1 | Infinity | Infinity | agree |  |
| FloatNegativeZeroTest | div2 | -Infinity | -Infinity | agree |  |
| FloatPowTest | pow1 | 8 | 8 | agree |  |
| FloatPowTest | pow2 | 1 | 1 | agree |  |
| FloatPowTest | pow3 | 1024 | 1024 | agree |  |
| FloatPowTest | pow4 | 0.5 | 0.5 | agree |  |
| FloatRoundTest | round1 | 3 | 3 | agree |  |
| FloatRoundTest | round2 | 2 | 2 | agree |  |
| FloatRoundTest | round3 | -3 | -3 | agree |  |
| FloatRoundTest | round4 | 3 | 3 | agree |  |
| FloatRoundTest | round5 | 4 | 4 | agree |  |
| FloatSqrtTest | sqrt1 | 2 | 2 | agree |  |
| FloatSqrtTest | sqrt2 | 3 | 3 | agree |  |
| FloatSqrtTest | sqrt3 | 0 | 0 | agree |  |
| FloatSubTest | sub1 | 7 | 7 | agree |  |
| FloatSubTest | sub2 | 10 | 10 | agree |  |
| FloatSubTest | sub3 | 1 | 1 | agree |  |
| FloatTruncateTest | trunc1 | 2 | 2 | agree |  |
| FloatTruncateTest | trunc2 | 2 | 2 | agree |  |
| FloatTruncateTest | trunc3 | -2 | -2 | agree |  |
| FloatTruncateTest | trunc4 | -2 | -2 | agree |  |
| FloorToIntTest | floor1 | 2 | 2 | agree |  |
| FloorToIntTest | floor2 | -3 | -3 | agree |  |
| IntAbsTest | abs1 | 5 | 5 | agree | kc_ElmCore02_78 |
| IntAbsTest | abs2 | 5 | 5 | agree | kc_ElmCore02_79 |
| IntAbsTest | abs3 | 0 | 0 | agree | kc_ElmCore02_80 |
| IntAddTest | add1 | 13 | 13 | agree | kc_ElmCore02_81 |
| IntAddTest | add2 | 0 | 0 | agree | kc_ElmCore02_82 |
| IntAddTest | add3 | -5 | -5 | agree | kc_ElmCore02_83 |
| IntCompareTest | lt | True | True | agree | kc_ElmCore02_84 |
| IntCompareTest | gt | True | True | agree | kc_ElmCore02_85 |
| IntCompareTest | le1 | True | True | agree | kc_ElmCore02_86 |
| IntCompareTest | le2 | True | True | agree | kc_ElmCore02_87 |
| IntCompareTest | ge1 | True | True | agree | kc_ElmCore02_88 |
| IntCompareTest | ge2 | True | True | agree | kc_ElmCore02_89 |
| IntCompareTest | eq | True | True | agree | kc_ElmCore02_90 |
| IntCompareTest | ne | True | True | agree | kc_ElmCore02_91 |
| IntDivByZeroTest | divZero1 | 0 | 0 | agree | kc_ElmCore02_92 |
| IntDivByZeroTest | divZero2 | 0 | 0 | agree | kc_ElmCore02_93 |

ElmCore02: 40 programs, 157 checks, 157 agree.

## ElmCore03

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| IntDivTest | div1 | 3 | 3 | agree | kc_ElmCore03_0 |
| IntDivTest | div2 | -3 | -3 | agree | kc_ElmCore03_1 |
| IntDivTest | div3 | -3 | -3 | agree | kc_ElmCore03_2 |
| IntDivTest | div4 | 3 | 3 | agree | kc_ElmCore03_3 |
| IntMinMaxTest | min1 | 3 | 3 | agree | kc_ElmCore03_4 |
| IntMinMaxTest | min2 | -5 | -5 | agree | kc_ElmCore03_5 |
| IntMinMaxTest | max1 | 10 | 10 | agree | kc_ElmCore03_6 |
| IntMinMaxTest | max2 | 5 | 5 | agree | kc_ElmCore03_7 |
| IntModByTest | mod1 | 3 | 3 | agree | kc_ElmCore03_8 |
| IntModByTest | mod2 | 1 | 1 | agree | kc_ElmCore03_9 |
| IntModByTest | mod3 | 3 | 3 | agree | kc_ElmCore03_10 |
| IntModByTest | mod4 | 1 | 1 | agree | kc_ElmCore03_11 |
| IntModByTest | mod5 | 0 | 0 | agree | kc_ElmCore03_12 |
| IntMulTest | mul1 | 30 | 30 | agree | kc_ElmCore03_13 |
| IntMulTest | mul2 | -15 | -15 | agree | kc_ElmCore03_14 |
| IntMulTest | mul3 | 6 | 6 | agree | kc_ElmCore03_15 |
| IntMulTest | mul4 | 0 | 0 | agree | kc_ElmCore03_16 |
| IntNegateTest | neg1 | -5 | -5 | agree | kc_ElmCore03_17 |
| IntNegateTest | neg2 | 5 | 5 | agree | kc_ElmCore03_18 |
| IntNegateTest | neg3 | 0 | 0 | agree | kc_ElmCore03_19 |
| IntPowTest | pow1 | 8 | 8 | agree | kc_ElmCore03_20 |
| IntPowTest | pow2 | 1 | 1 | agree | kc_ElmCore03_21 |
| IntPowTest | pow3 | 1024 | 1024 | agree | kc_ElmCore03_22 |
| IntPowTest | pow4 | -8 | -8 | agree | kc_ElmCore03_23 |
| IntRemainderByTest | rem1 | 3 | 3 | agree | kc_ElmCore03_24 |
| IntRemainderByTest | rem2 | -3 | -3 | agree | kc_ElmCore03_25 |
| IntRemainderByTest | rem3 | 3 | 3 | agree | kc_ElmCore03_26 |
| IntRemainderByTest | rem4 | -3 | -3 | agree | kc_ElmCore03_27 |
| IntSubTest | sub1 | 7 | 7 | agree | kc_ElmCore03_28 |
| IntSubTest | sub2 | 10 | 10 | agree | kc_ElmCore03_29 |
| IntSubTest | sub3 | 1 | 1 | agree | kc_ElmCore03_30 |
| ListAppendTest | append1 | [1,2,3,4] | [1,2,3,4] | agree |  |
| ListAppendTest | append_empty | [1,2] | [1,2] | agree |  |
| ListAppendTest | concat_op | [1,2,3] | [1,2,3] | agree |  |
| ListConcatTest | append | [1,2,3,4] | [1,2,3,4] | agree |  |
| ListConcatTest | concat | [1,2,3,4,5,6] | [1,2,3,4,5,6] | agree |  |
| ListConcatTest | empty | [1,2,3] | [1,2,3] | agree |  |
| NotEqualBoolCaseTest | cTT | "no" | "no" | agree | kc_ElmCore03_31 |
| NotEqualBoolCaseTest | cTF | "yes" | "yes" | agree | kc_ElmCore03_32 |
| NotEqualBoolCaseTest | cFT | "yes" | "yes" | agree | kc_ElmCore03_33 |
| NotEqualBoolCaseTest | cFF | "no" | "no" | agree | kc_ElmCore03_34 |
| NotEqualBoolIfTest | ifTT | "no" | "no" | agree | kc_ElmCore03_35 |
| NotEqualBoolIfTest | ifTF | "yes" | "yes" | agree | kc_ElmCore03_36 |
| NotEqualBoolIfTest | ifFT | "yes" | "yes" | agree | kc_ElmCore03_37 |
| NotEqualBoolIfTest | ifFF | "no" | "no" | agree | kc_ElmCore03_38 |
| NotEqualBoolMaybeTest | jt_jt | False | False | agree | kc_ElmCore03_39 |
| NotEqualBoolMaybeTest | jt_jf | True | True | agree | kc_ElmCore03_40 |
| NotEqualBoolMaybeTest | jf_jt | True | True | agree | kc_ElmCore03_41 |
| NotEqualBoolMaybeTest | jf_jf | False | False | agree | kc_ElmCore03_42 |
| NotEqualBoolMaybeTest | n_jt | True | True | agree | kc_ElmCore03_43 |
| NotEqualBoolMaybeTest | n_n | False | False | agree | kc_ElmCore03_44 |
| NotEqualBoolMaybeTest | jt_n | True | True | agree | kc_ElmCore03_45 |
| NotEqualBoolPapTest | isNotTrueList | [False,True,False,True] | [False,True,False,True] | agree |  |
| NotEqualBoolPapTest | isNotFalseList | [True,False,True,False] | [True,False,True,False] | agree |  |
| NotEqualBoolPapTest | filterNotTrue | [False,False] | [False,False] | agree |  |
| NotEqualBoolPapTest | filterNotFalse | [True,True] | [True,True] | agree |  |
| NotEqualBoolPapTest | anyNotTrue | True | True | agree | kc_ElmCore03_46 |
| NotEqualBoolPapTest | anyNotFalse | True | True | agree | kc_ElmCore03_47 |
| NotEqualBoolRecordTest | tt | False | False | agree | kc_ElmCore03_48 |
| NotEqualBoolRecordTest | tf | True | True | agree | kc_ElmCore03_49 |
| NotEqualBoolRecordTest | ft | True | True | agree | kc_ElmCore03_50 |
| NotEqualBoolRecordTest | ff | False | False | agree | kc_ElmCore03_51 |
| NotEqualBoolTest | ntt | False | False | agree | kc_ElmCore03_52 |
| NotEqualBoolTest | ntf | True | True | agree | kc_ElmCore03_53 |
| NotEqualBoolTest | nft | True | True | agree | kc_ElmCore03_54 |
| NotEqualBoolTest | nff | False | False | agree | kc_ElmCore03_55 |
| NotEqualBoolTest | bntt | True | True | agree | kc_ElmCore03_56 |
| NotEqualBoolTest | bntf | False | False | agree | kc_ElmCore03_57 |
| NotEqualBoolTest | bnft | False | False | agree | kc_ElmCore03_58 |
| NotEqualBoolTest | bnff | True | True | agree | kc_ElmCore03_59 |
| NotEqualBoolVarTest | vTT | False | False | agree | kc_ElmCore03_60 |
| NotEqualBoolVarTest | vTF | True | True | agree | kc_ElmCore03_61 |
| NotEqualBoolVarTest | vFT | True | True | agree | kc_ElmCore03_62 |
| NotEqualBoolVarTest | vFF | False | False | agree | kc_ElmCore03_63 |
| NotEqualBoolVarTest | hTT | False | False | agree | kc_ElmCore03_64 |
| NotEqualBoolVarTest | hTF | True | True | agree | kc_ElmCore03_65 |
| NotEqualBoolVarTest | hFT | True | True | agree | kc_ElmCore03_66 |
| NotEqualBoolVarTest | hFF | False | False | agree | kc_ElmCore03_67 |
| OrderingEmptyListPapTest | ltEmpty | [False,True,True] | [False,True,True] | agree |  |
| OrderingEmptyListPapTest | leEmpty | [True,True,True] | [True,True,True] | agree |  |
| OrderingEmptyListPapTest | gtEmpty | [False,False,False] | [False,False,False] | agree |  |
| OrderingEmptyListPapTest | geEmpty | [True,False,False] | [True,False,False] | agree |  |
| OrderingEmptyListPapTest | cmpEmpty | [EQ,LT,LT] | [EQ,LT,LT] | agree |  |
| OrderingEmptyListTest | lt_ee | False | False | agree | kc_ElmCore03_68 |
| OrderingEmptyListTest | lt_ea | True | True | agree | kc_ElmCore03_69 |
| OrderingEmptyListTest | lt_ae | False | False | agree | kc_ElmCore03_70 |
| OrderingEmptyListTest | le_ee | True | True | agree | kc_ElmCore03_71 |
| OrderingEmptyListTest | le_ea | True | True | agree | kc_ElmCore03_72 |
| OrderingEmptyListTest | le_ae | False | False | agree | kc_ElmCore03_73 |
| OrderingEmptyListTest | gt_ee | False | False | agree | kc_ElmCore03_74 |
| OrderingEmptyListTest | gt_ea | False | False | agree | kc_ElmCore03_75 |
| OrderingEmptyListTest | gt_ae | True | True | agree | kc_ElmCore03_76 |
| OrderingEmptyListTest | ge_ee | True | True | agree | kc_ElmCore03_77 |
| OrderingEmptyListTest | ge_ea | False | False | agree | kc_ElmCore03_78 |
| OrderingEmptyListTest | ge_ae | True | True | agree | kc_ElmCore03_79 |
| OrderingEmptyListTest | lt_ab | True | True | agree | kc_ElmCore03_80 |
| OrderingEmptyListTest | ge_ab | False | False | agree | kc_ElmCore03_81 |
| OrderingEmptyStringPapTest | ltEmpty | [False,True,True] | [False,True,True] | agree |  |
| OrderingEmptyStringPapTest | leEmpty | [True,True,True] | [True,True,True] | agree |  |
| OrderingEmptyStringPapTest | gtEmpty | [False,False,False] | [False,False,False] | agree |  |
| OrderingEmptyStringPapTest | geEmpty | [True,False,False] | [True,False,False] | agree |  |
| OrderingEmptyStringPapTest | cmpEmpty | [EQ,LT,LT] | [EQ,LT,LT] | agree |  |
| OrderingEmptyStringTest | lt_ee | False | False | agree | kc_ElmCore03_82 |
| OrderingEmptyStringTest | lt_ea | True | True | agree | kc_ElmCore03_83 |
| OrderingEmptyStringTest | lt_ae | False | False | agree | kc_ElmCore03_84 |
| OrderingEmptyStringTest | le_ee | True | True | agree | kc_ElmCore03_85 |
| OrderingEmptyStringTest | le_ea | True | True | agree | kc_ElmCore03_86 |
| OrderingEmptyStringTest | le_ae | False | False | agree | kc_ElmCore03_87 |
| OrderingEmptyStringTest | gt_ee | False | False | agree | kc_ElmCore03_88 |
| OrderingEmptyStringTest | gt_ea | False | False | agree | kc_ElmCore03_89 |
| OrderingEmptyStringTest | gt_ae | True | True | agree | kc_ElmCore03_90 |
| OrderingEmptyStringTest | ge_ee | True | True | agree | kc_ElmCore03_91 |
| OrderingEmptyStringTest | ge_ea | False | False | agree | kc_ElmCore03_92 |
| OrderingEmptyStringTest | ge_ae | True | True | agree | kc_ElmCore03_93 |
| OrderingEmptyStringTest | lt_ab | True | True | agree | kc_ElmCore03_94 |
| OrderingEmptyStringTest | ge_ab | False | False | agree | kc_ElmCore03_95 |
| OrderingMixedCaptureTest | int_lt_count | 3 | 3 | agree | kc_ElmCore03_96 |
| OrderingMixedCaptureTest | int_ge_count | 2 | 2 | agree | kc_ElmCore03_97 |
| OrderingMixedCaptureTest | float_lt_count | 3 | 3 | agree | kc_ElmCore03_98 |
| OrderingMixedCaptureTest | float_ge_count | 2 | 2 | agree | kc_ElmCore03_99 |
| OrderingMixedCaptureTest | char_lt_count | 3 | 3 | agree | kc_ElmCore03_100 |
| OrderingMixedCaptureTest | char_ge_count | 2 | 2 | agree | kc_ElmCore03_101 |
| OrderingTupleWithEmptyListTest | lt_ee | False | False | agree | kc_ElmCore03_102 |
| OrderingTupleWithEmptyListTest | lt_eA | True | True | agree | kc_ElmCore03_103 |
| OrderingTupleWithEmptyListTest | lt_Ae | False | False | agree | kc_ElmCore03_104 |
| OrderingTupleWithEmptyListTest | le_ee | True | True | agree | kc_ElmCore03_105 |
| OrderingTupleWithEmptyListTest | le_eA | True | True | agree | kc_ElmCore03_106 |
| OrderingTupleWithEmptyListTest | le_Ae | False | False | agree | kc_ElmCore03_107 |
| OrderingTupleWithEmptyListTest | gt_ee | False | False | agree | kc_ElmCore03_108 |
| OrderingTupleWithEmptyListTest | gt_eA | False | False | agree | kc_ElmCore03_109 |
| OrderingTupleWithEmptyListTest | gt_Ae | True | True | agree | kc_ElmCore03_110 |
| OrderingTupleWithEmptyListTest | ge_ee | True | True | agree | kc_ElmCore03_111 |
| OrderingTupleWithEmptyListTest | ge_eA | False | False | agree | kc_ElmCore03_112 |
| OrderingTupleWithEmptyListTest | ge_Ae | True | True | agree | kc_ElmCore03_113 |
| OrderingTupleWithEmptyStringTest | lt_ee | False | False | agree | kc_ElmCore03_114 |
| OrderingTupleWithEmptyStringTest | lt_eA | True | True | agree | kc_ElmCore03_115 |
| OrderingTupleWithEmptyStringTest | lt_Ae | False | False | agree | kc_ElmCore03_116 |
| OrderingTupleWithEmptyStringTest | le_ee | True | True | agree | kc_ElmCore03_117 |
| OrderingTupleWithEmptyStringTest | le_eA | True | True | agree | kc_ElmCore03_118 |
| OrderingTupleWithEmptyStringTest | le_Ae | False | False | agree | kc_ElmCore03_119 |
| OrderingTupleWithEmptyStringTest | gt_ee | False | False | agree | kc_ElmCore03_120 |
| OrderingTupleWithEmptyStringTest | gt_eA | False | False | agree | kc_ElmCore03_121 |
| OrderingTupleWithEmptyStringTest | gt_Ae | True | True | agree | kc_ElmCore03_122 |
| OrderingTupleWithEmptyStringTest | ge_ee | True | True | agree | kc_ElmCore03_123 |
| OrderingTupleWithEmptyStringTest | ge_eA | False | False | agree | kc_ElmCore03_124 |
| OrderingTupleWithEmptyStringTest | ge_Ae | True | True | agree | kc_ElmCore03_125 |
| PipelineTest | pipe1 | 12 | 12 | agree | kc_ElmCore03_126 |
| PipelineTest | pipe2 | [2,4,6] | [2,4,6] | agree |  |
| PipelineTest | backpipe | 10 | 10 | agree | kc_ElmCore03_127 |
| RoundToIntTest | round1 | 3 | 3 | agree |  |
| RoundToIntTest | round2 | 2 | 2 | agree |  |
| RoundToIntTest | round3 | -3 | -3 | agree |  |
| StandardA40IntOverflowTest | big * big - big * big + 1 == 1 | True | True | agree | kc_ElmCore03_128 |
| StandardA40IntOverflowTest | huge + huge - (huge + huge) + 1 == 1 | True | True | agree | kc_ElmCore03_129 |
| StandardA41IntDivisionWideTest | 5000000000 // 1 == 5000000000 | True | True | agree | kc_ElmCore03_130 |
| StandardA41IntDivisionWideTest | -5000000000 // 1 == -5000000000 | True | True | agree | kc_ElmCore03_131 |
| StandardA42ModByZeroTest | modBy 0 7 + 1 == 1 | True | True | agree | kc_ElmCore03_132 |
| StandardA42ModByZeroTest | modBy 0 -7 + 1 == 1 | True | True | agree | kc_ElmCore03_133 |
| StandardA42RemainderByZeroTest | remainderBy 0 7 + 1 == 1 | True | True | agree | kc_ElmCore03_134 |
| StandardA42RemainderByZeroTest | remainderBy 0 7 | 0 | 0 | agree | kc_ElmCore03_135 |
| StandardA42ZeroDivisorTest | 3 // 0 | 0 | 0 | agree | kc_ElmCore03_136 |
| StandardA42ZeroDivisorTest | modBy 0 3 | 0 | 0 | agree | kc_ElmCore03_137 |
| StandardA42ZeroDivisorTest | remainderBy 0 3 | 0 | 0 | agree | kc_ElmCore03_138 |
| StandardA43PowNegativeTest | 1 ^ -1 | 1 | 1 | agree | kc_ElmCore03_139 |
| StandardA43PowNegativeTest | (-1) ^ -3 | -1 | -1 | agree | kc_ElmCore03_140 |
| StandardA43PowNegativeTest | (-1) ^ -2 | 1 | 1 | agree | kc_ElmCore03_141 |
| StandardA43PowNegativeTest | 2 ^ -1 + 1 == 1 | True | True | agree | kc_ElmCore03_142 |
| StandardA43PowNegativeTest | 0 ^ -1 + 1 == 1 | True | True | agree | kc_ElmCore03_143 |
| StandardA44RoundNonFiniteTest | round nan + 1 == 1 | True | True | agree |  |
| StandardA44RoundNonFiniteTest | floor nan + 1 == 1 | True | True | agree |  |
| StandardA44RoundNonFiniteTest | ceiling nan + 1 == 1 | True | True | agree |  |
| StandardA44RoundNonFiniteTest | round inf - round inf + 1 == 1 | True | True | agree |  |
| StandardA44RoundNonFiniteTest | floor -inf - floor -inf + 1 == 1 | True | True | agree |  |
| StandardA44RoundNonFiniteTest | ceiling inf - ceiling inf + 1 == 1 | True | True | agree |  |
| StandardA44TruncateWideTest | truncate 3.0e10 >= 2147483647 | True | True | agree |  |
| StandardA44TruncateWideTest | truncate -3.0e10 <= -2147483648 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | negate 0 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | 0 * -1 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | modBy 4 -4 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | remainderBy 4 -4 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | round -0.4 | True | True | agree |  |
| StandardA45IntNegativeZeroTest | ceiling -0.5 | True | True | agree |  |
| StandardA46CompareNanTest | compare 1 nan | LT | LT | agree | kc_ElmCore03_144 |
| StandardA46CompareNanTest | compare nan nan | EQ | EQ | agree | kc_ElmCore03_145 |
| StandardA46CompareNanTest | compare nan 1 | GT | GT | agree | kc_ElmCore03_146 |
| StandardA48MinMaxNanTest | min nan 1 is NaN | True | True | agree | kc_ElmCore03_147 |
| StandardA48MinMaxNanTest | min 1 nan is NaN | True | True | agree | kc_ElmCore03_148 |
| StandardA48MinMaxNanTest | max nan 1 is NaN | True | True | agree | kc_ElmCore03_149 |
| StandardA48MinMaxNanTest | max 1 nan is NaN | True | True | agree | kc_ElmCore03_150 |
| StandardA48MinMaxNanTest | min 0 -0 is -0 | True | True | agree | kc_ElmCore03_151 |
| StandardA48MinMaxNanTest | min -0 0 is -0 | True | True | agree | kc_ElmCore03_152 |
| StandardA48MinMaxNanTest | max 0 -0 is +0 | True | True | agree | kc_ElmCore03_153 |
| StandardA48MinMaxNanTest | max -0 0 is +0 | True | True | agree | kc_ElmCore03_154 |
| StandardA49ClampTest | clamp 10 0 5 at Float is +0 | True | True | agree | kc_ElmCore03_155 |
| StandardA49ClampTest | clamp nan 1 0.5 is NaN | True | True | agree | kc_ElmCore03_156 |
| StandardA49ClampTest | clamp 0 1 -0 is +0 | True | True | agree | kc_ElmCore03_157 |
| StandardA49ClampTest | clamp -1 -0 0 is -0 | True | True | agree | kc_ElmCore03_158 |
| StandardA49ClampTest | clamp 10 0 5 at Int | 10 | 10 | agree | kc_ElmCore03_159 |
| StandardA49ClampTest | clamp 10 0 20 at Int | 0 | 0 | agree | kc_ElmCore03_160 |
| StandardA49ClampTest | clamp 0 10 -5 at Int | 0 | 0 | agree | kc_ElmCore03_161 |
| StandardA49ClampTest | clamp 0 10 15 at Int | 10 | 10 | agree | kc_ElmCore03_162 |
| StandardA49ClampTest | clamp 0 10 7 at Int | 7 | 7 | agree | kc_ElmCore03_163 |
| StandardA51FunctionEqualityTest | compared | True | True | agree | kc_ElmCore03_164 |
| StandardA53CharOrderTest | compare '😀' 'ﬀ' | GT | GT | agree | kc_ElmCore03_165 |
| StandardA53CharOrderTest | '😀' > 'ﬀ' | True | True | agree | kc_ElmCore03_166 |
| StandardA53CharOrderTest | toCode order agrees | True | True | agree | kc_ElmCore03_167 |

ElmCore03: 40 programs, 206 checks, 206 agree.

## ElmCore04

| Program | Label | Expected (CHECK) | Definition | Status | Theorem |
|---|---|---|---|---|---|
| StandardA53StringOrderTest | compare "😀" "ﬀ" | GT | GT | agree | kc_ElmCore04_0 |
| StandardA53StringOrderTest | "😀" > "ﬀ" | True | True | agree | kc_ElmCore04_1 |
| StandardA53StringOrderTest | sorted | ["ﬀ","😀"] | ["ﬀ","😀"] | agree |  |
| StandardA65PowOneTest | 1 ^ inf == 1 | True | True | agree |  |
| StandardA65PowOneTest | 1 ^ nan == 1 | True | True | agree |  |
| StandardA65PowOneTest | (-1) ^ inf == 1 | True | True | agree |  |
| StringConcatContentTest | concat20 | "abcdefghijABCDEFGHIJ" | "abcdefghijABCDEFGHIJ" | agree | kc_ElmCore04_2 |
| StringConcatContentTest | concat100 | "xyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxy" | "xyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxy" | agree | kc_ElmCore04_3 |
| StringConcatTest | concat1 | "HelloWorld" | "HelloWorld" | agree | kc_ElmCore04_4 |
| StringConcatTest | concat2 | "Hello World" | "Hello World" | agree | kc_ElmCore04_5 |
| StringConcatTest | append | "foobar" | "foobar" | agree | kc_ElmCore04_6 |
| ToFloatTest | toFloat1 | 42 | 42 | agree |  |
| ToFloatTest | toFloat2 | -10 | -10 | agree |  |
| ToFloatTest | toFloat3 | 0 | 0 | agree |  |
| TruncateToIntTest | trunc1 | 2 | 2 | agree |  |
| TruncateToIntTest | trunc2 | -2 | -2 | agree |  |
| UtilsEqualityCaptureCharTest | eq_count | 2 | 2 | agree | kc_ElmCore04_7 |
| UtilsEqualityCaptureCharTest | ne_count | 3 | 3 | agree | kc_ElmCore04_8 |
| UtilsEqualityCaptureCharTest | eq_filter | ['x','x'] | ['x','x'] | agree |  |
| UtilsEqualityCaptureCharTest | ne_filter | ['a','b','c'] | ['a','b','c'] | agree |  |
| UtilsEqualityCaptureFloatTest | eq_count | 2 | 2 | agree | kc_ElmCore04_9 |
| UtilsEqualityCaptureFloatTest | ne_count | 3 | 3 | agree | kc_ElmCore04_10 |
| UtilsEqualityCaptureFloatTest | eq_filter | [1.5,1.5] | [1.5,1.5] | agree |  |
| UtilsEqualityCaptureFloatTest | ne_filter | [0,2,3] | [0,2,3] | agree |  |
| UtilsEqualityCaptureIntTest | eq_count | 2 | 2 | agree | kc_ElmCore04_11 |
| UtilsEqualityCaptureIntTest | ne_count | 3 | 3 | agree | kc_ElmCore04_12 |
| UtilsEqualityCaptureIntTest | eq_filter | [5,5] | [5,5] | agree |  |
| UtilsEqualityCaptureIntTest | ne_filter | [1,2,3] | [1,2,3] | agree |  |
| UtilsOrderingCaptureCharTest | lt_filter | ['a','b'] | ['a','b'] | agree |  |
| UtilsOrderingCaptureCharTest | le_filter | ['a','b','c'] | ['a','b','c'] | agree |  |
| UtilsOrderingCaptureCharTest | gt_filter | ['d','e'] | ['d','e'] | agree |  |
| UtilsOrderingCaptureCharTest | ge_filter | ['c','d','e'] | ['c','d','e'] | agree |  |
| UtilsOrderingCaptureCharTest | count_lt | 2 | 2 | agree | kc_ElmCore04_13 |
| UtilsOrderingCaptureCharTest | count_ge | 3 | 3 | agree | kc_ElmCore04_14 |
| UtilsOrderingCaptureFloatTest | lt_filter | [1,2] | [1,2] | agree |  |
| UtilsOrderingCaptureFloatTest | le_filter | [1,2,3] | [1,2,3] | agree |  |
| UtilsOrderingCaptureFloatTest | gt_filter | [4,5] | [4,5] | agree |  |
| UtilsOrderingCaptureFloatTest | ge_filter | [3,4,5] | [3,4,5] | agree |  |
| UtilsOrderingCaptureFloatTest | count_lt | 2 | 2 | agree | kc_ElmCore04_15 |
| UtilsOrderingCaptureFloatTest | count_ge | 3 | 3 | agree | kc_ElmCore04_16 |
| UtilsOrderingCaptureIntTest | lt_filter | [1,2] | [1,2] | agree |  |
| UtilsOrderingCaptureIntTest | le_filter | [1,2,3] | [1,2,3] | agree |  |
| UtilsOrderingCaptureIntTest | gt_filter | [4,5] | [4,5] | agree |  |
| UtilsOrderingCaptureIntTest | ge_filter | [3,4,5] | [3,4,5] | agree |  |
| UtilsOrderingCaptureIntTest | count_lt | 2 | 2 | agree | kc_ElmCore04_17 |
| UtilsOrderingCaptureIntTest | count_ge | 3 | 3 | agree | kc_ElmCore04_18 |

ElmCore04: 12 programs, 46 checks, 46 agree.

Total: 1477 checks, 1477 agree, 0 diverge (0 known); 1106 theorems by decide +kernel.
