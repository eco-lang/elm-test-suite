# Standard Elm mechanisation: example run

Corpus programs: 40; ruling programs: 12.

## Corpus (the test programs that accompany the book)

| Program | Label | Implementation (CHECK) | Definition | Status |
|---|---|---|---|---|
| IntAddTest | add1 | 13 | 13 | agree |
| IntAddTest | add2 | 0 | 0 | agree |
| IntAddTest | add3 | -5 | -5 | agree |
| IntMulTest | mul1 | 30 | 30 | agree |
| IntMulTest | mul2 | -15 | -15 | agree |
| IntMulTest | mul3 | 6 | 6 | agree |
| IntMulTest | mul4 | 0 | 0 | agree |
| IntDivTest | div1 | 3 | 3 | agree |
| IntDivTest | div2 | -3 | -3 | agree |
| IntDivTest | div3 | -3 | -3 | agree |
| IntDivTest | div4 | 3 | 3 | agree |
| IntDivByZeroTest | divZero1 | 0 | 0 | agree |
| IntDivByZeroTest | divZero2 | 0 | 0 | agree |
| IntModByTest | mod1 | 3 | 3 | agree |
| IntModByTest | mod2 | 1 | 1 | agree |
| IntModByTest | mod3 | 3 | 3 | agree |
| IntModByTest | mod4 | 1 | 1 | agree |
| IntModByTest | mod5 | 0 | 0 | agree |
| IntRemainderByTest | rem1 | 3 | 3 | agree |
| IntRemainderByTest | rem2 | -3 | -3 | agree |
| IntRemainderByTest | rem3 | 3 | 3 | agree |
| IntRemainderByTest | rem4 | -3 | -3 | agree |
| IntPowTest | pow1 | 8 | 8 | agree |
| IntPowTest | pow2 | 1 | 1 | agree |
| IntPowTest | pow3 | 1024 | 1024 | agree |
| IntPowTest | pow4 | -8 | -8 | agree |
| IntNegateTest | neg1 | -5 | -5 | agree |
| IntNegateTest | neg2 | 5 | 5 | agree |
| IntNegateTest | neg3 | 0 | 0 | agree |
| IntAbsTest | abs1 | 5 | 5 | agree |
| IntAbsTest | abs2 | 5 | 5 | agree |
| IntAbsTest | abs3 | 0 | 0 | agree |
| IntCompareTest | lt | True | True | agree |
| IntCompareTest | gt | True | True | agree |
| IntCompareTest | le1 | True | True | agree |
| IntCompareTest | le2 | True | True | agree |
| IntCompareTest | ge1 | True | True | agree |
| IntCompareTest | ge2 | True | True | agree |
| IntCompareTest | eq | True | True | agree |
| IntCompareTest | ne | True | True | agree |
| IntMinMaxTest | min1 | 3 | 3 | agree |
| IntMinMaxTest | min2 | -5 | -5 | agree |
| IntMinMaxTest | max1 | 10 | 10 | agree |
| IntMinMaxTest | max2 | 5 | 5 | agree |
| BoolAndTest | and1 | True | True | agree |
| BoolAndTest | and2 | False | False | agree |
| BoolAndTest | and3 | False | False | agree |
| BoolAndTest | and4 | False | False | agree |
| BoolOrTest | or1 | True | True | agree |
| BoolOrTest | or2 | True | True | agree |
| BoolOrTest | or3 | True | True | agree |
| BoolOrTest | or4 | False | False | agree |
| BoolNotTest | not1 | False | False | agree |
| BoolNotTest | not2 | True | True | agree |
| BoolXorTest | xor1 | False | False | agree |
| BoolXorTest | xor2 | True | True | agree |
| BoolXorTest | xor3 | True | True | agree |
| BoolXorTest | xor4 | False | False | agree |
| BoolShortCircuitTest | shortAnd | False | False | agree |
| BoolShortCircuitTest | shortOr | True | True | agree |
| CompareCharTest | cmp1 | LT | LT | agree |
| CompareCharTest | cmp2 | GT | GT | agree |
| CompareCharTest | cmp3 | EQ | EQ | agree |
| CompareEmptyListTest | ee | EQ | EQ | agree |
| CompareEmptyListTest | ea | LT | LT | agree |
| CompareEmptyListTest | ae | GT | GT | agree |
| CompareEmptyListTest | eab | LT | LT | agree |
| CompareEmptyListTest | abe | GT | GT | agree |
| CompareEmptyListTest | aa | EQ | EQ | agree |
| CompareEmptyListTest | ab | LT | LT | agree |
| CompareEmptyListTest | ba | GT | GT | agree |
| CompareEmptyListTest | aba | GT | GT | agree |
| CompareTupleWithEmptyListTest | ee | EQ | EQ | agree |
| CompareTupleWithEmptyListTest | eA | LT | LT | agree |
| CompareTupleWithEmptyListTest | Ae | GT | GT | agree |
| CompareTupleWithEmptyListTest | eAB | LT | LT | agree |
| CompareTupleWithEmptyListTest | ABe | GT | GT | agree |
| CompareTupleWithEmptyListTest | f0_ee | LT | LT | agree |
| CompareTupleWithEmptyListTest | f0_Ae | GT | GT | agree |
| EqualityTest | eq1 | True | True | agree |
| EqualityTest | eq2 | False | False | agree |
| EqualityTest | ne1 | True | True | agree |
| EqualityTest | ne2 | False | False | agree |
| EqualityTest | listEq | True | True | agree |
| EqualityBoolContainerTest | pairTT_TT | True | True | agree |
| EqualityBoolContainerTest | pairTT_TF | False | False | agree |
| EqualityBoolContainerTest | pairTF_TT | False | False | agree |
| EqualityBoolContainerTest | pairTF_FT | False | False | agree |
| EqualityBoolContainerTest | tripleTFT_TFT | True | True | agree |
| EqualityBoolContainerTest | tripleTFT_TFF | False | False | agree |
| EqualityBoolContainerTest | listTT_TT | True | True | agree |
| EqualityBoolContainerTest | listTF_TF | True | True | agree |
| EqualityBoolContainerTest | listTF_FT | False | False | agree |
| EqualityBoolContainerTest | listTF_TT | False | False | agree |
| EqualityBoolContainerTest | listEmpty | True | True | agree |
| EqualityBoolRecordTest | recEq | True | True | agree |
| EqualityBoolRecordTest | recDiffA | False | False | agree |
| EqualityBoolRecordTest | recDiffB | False | False | agree |
| EqualityBoolRecordTest | recDiffBoth | False | False | agree |
| EqualityBoolRecordTest | recFF_FF | True | True | agree |
| CaseCustomTypeTest | shape1 | 100 | 100 | agree |
| CaseCustomTypeTest | shape2 | 50 | 50 | agree |
| CaseListConsTest | sum1 | 0 | 0 | agree |
| CaseListConsTest | sum2 | 1 | 1 | agree |
| CaseListConsTest | sum3 | 6 | 6 | agree |
| CaseNestedTest | nested1 | "both" | "both" | agree |
| CaseNestedTest | nested2 | "first" | "first" | agree |
| CaseNestedTest | nested3 | "second" | "second" | agree |
| CaseNestedTest | nested4 | "neither" | "neither" | agree |
| CaseTupleTest | pair1 | "both zero" | "both zero" | agree |
| CaseTupleTest | pair2 | "x is zero" | "x is zero" | agree |
| CaseTupleTest | pair3 | "y is zero" | "y is zero" | agree |
| CaseTupleTest | pair4 | "neither zero" | "neither zero" | agree |
| CaseTreeTest | tree1 | 0 | 0 | agree |
| CaseTreeTest | tree2 | 1 | 1 | agree |
| CaseTreeTest | tree3 | 3 | 3 | agree |
| CaseCharTest | char1 | "vowel a" | "vowel a" | agree |
| CaseCharTest | char2 | "vowel e" | "vowel e" | agree |
| CaseCharTest | char3 | "other" | "other" | agree |
| CaseCharTest | char4 | "other" | "other" | agree |
| LetDestructuringTest | first | 1 | 1 | agree |
| LetDestructuringTest | second | 2 | 2 | agree |
| LetDestructuringTest | head | 10 | 10 | agree |
| LetDestructRecordTest | single | 42 | 42 | agree |
| LetDestructRecordTest | multi | 3 | 3 | agree |
| LetDestructRecordTest | partial | 4 | 4 | agree |
| LetDestructRecordTest | mixed | 3 | 3 | agree |
| LetRecMultiArgTest | result | 2 | 2 | agree |
| LetRecClosureTest | LetRecClosureTest | [1,2,3] | [1,2,3] | agree |
| RecordUpdateTest | updated | { x = 10, y = 2 } | { x = 10, y = 2 } | agree |
| RecordUpdateTest | original | { x = 1, y = 2 } | { x = 1, y = 2 } | agree |
| RecordChainedUpdateTest | multi | { x = 100, y = 20, z = 300 } | { x = 100, y = 20, z = 300 } | agree |
| RecordChainedUpdateTest | chain | { x = 10, y = 20 } | { x = 10, y = 20 } | agree |
| RecordAccessTest | x | 1 | 1 | agree |
| RecordAccessTest | y | 2 | 2 | agree |
| RecordAccessTest | name | "Alice" | "Alice" | agree |
| ClosureCapture01Test | unwrap1 | 42 | 42 | agree |
| ClosureCapture01Test | unwrap2 | 99 | 99 | agree |
| RecursiveFactorialTest | fact0 | 1 | 1 | agree |
| RecursiveFactorialTest | fact5 | 120 | 120 | agree |
| RecursiveFactorialTest | fact10 | 3628800 | 3628800 | agree |
| MutualRecursionTest | isEven0 | True | True | agree |
| MutualRecursionTest | isEven5 | False | False | agree |
| MutualRecursionTest | isOdd5 | True | True | agree |
| TailRecursiveSumTest | sum1 | 15 | 15 | agree |
| TailRecursiveSumTest | sum2 | 55 | 55 | agree |
| TailRecursiveSumTest | sum3 | 5050 | 5050 | agree |
| PartialAppChainTest | chain1 | 10 | 10 | agree |
| PartialAppChainTest | chain2 | 6 | 6 | agree |

Corpus (the test programs that accompany the book): 149 checks, 149 agree, 0 diverge.

## Rulings (A40, A42, A43, A46 to A51)

| Program | Label | Implementation (CHECK) | Definition | Status |
|---|---|---|---|---|
| StandardA42ZeroDivisorTest | 3 // 0 | 0 | 0 | agree |
| StandardA42ZeroDivisorTest | modBy 0 3 | 0 | 0 | agree |
| StandardA42ZeroDivisorTest | remainderBy 0 3 | 0 | 0 | agree |
| StandardA42ModByZeroTest | modBy 0 7 + 1 == 1 | True | True | agree |
| StandardA42ModByZeroTest | modBy 0 -7 + 1 == 1 | True | True | agree |
| StandardA42RemainderByZeroTest | remainderBy 0 7 + 1 == 1 | True | True | agree |
| StandardA42RemainderByZeroTest | remainderBy 0 7 | 0 | 0 | agree |
| StandardA43PowNegativeTest | 1 ^ -1 | 1 | 1 | agree |
| StandardA43PowNegativeTest | (-1) ^ -3 | -1 | -1 | agree |
| StandardA43PowNegativeTest | (-1) ^ -2 | 1 | 1 | agree |
| StandardA43PowNegativeTest | 2 ^ -1 + 1 == 1 | True | True | agree |
| StandardA43PowNegativeTest | 0 ^ -1 + 1 == 1 | True | True | agree |
| StandardA51FunctionEqualityTest | compared | True | True | agree |
| StandardA40IntOverflowTest | big * big - big * big + 1 == 1 | True | True | agree |
| StandardA40IntOverflowTest | huge + huge - (huge + huge) + 1 == 1 | True | True | agree |
| StandardA46CompareNanTest | compare 1 nan | LT | LT | agree |
| StandardA46CompareNanTest | compare nan nan | EQ | EQ | agree |
| StandardA46CompareNanTest | compare nan 1 | GT | GT | agree |
| StandardA48MinMaxNanTest | min 0 -0 is -0 | True | True | agree |
| StandardA48MinMaxNanTest | min -0 0 is -0 | True | True | agree |
| StandardA48MinMaxNanTest | max 0 -0 is +0 | True | True | agree |
| StandardA48MinMaxNanTest | max -0 0 is +0 | True | True | agree |
| CoreIssue1080ClampNanTest | clamp nan | NaN | NaN | agree |
| StandardA49ClampTest | clamp 10 0 5 at Float is +0 | True | True | agree |
| StandardA49ClampTest | clamp nan 1 0.5 is NaN | True | True | agree |
| StandardA49ClampTest | clamp 0 1 -0 is +0 | True | True | agree |
| StandardA49ClampTest | clamp -1 -0 0 is -0 | True | True | agree |
| StandardA49ClampTest | clamp 10 0 5 at Int | 10 | 10 | agree |
| StandardA49ClampTest | clamp 10 0 20 at Int | 0 | 0 | agree |
| StandardA49ClampTest | clamp 0 10 -5 at Int | 0 | 0 | agree |
| StandardA49ClampTest | clamp 0 10 15 at Int | 10 | 10 | agree |
| StandardA49ClampTest | clamp 0 10 7 at Int | 7 | 7 | agree |
| CompilerIssue2362NanTupleEqualityTest | nan == nan | False | False | agree |
| CompilerIssue2362NanTupleEqualityTest | p == q | False | False | agree |
| CompilerIssue2362NanTupleEqualityTest | p == p | False | False | agree |
| CoreIssue988NanContainerSelfEqualityTest | record | False | False | agree |
| CoreIssue988NanContainerSelfEqualityTest | custom type | False | False | agree |
| CoreIssue988NanContainerSelfEqualityTest | maybe | False | False | agree |
| CoreIssue988NanContainerSelfEqualityTest | shared inner tuple | False | False | agree |
| CoreIssue988NanContainerSelfEqualityTest | shared inner list | False | False | agree |

Rulings (A40, A42, A43, A46 to A51): 40 checks, 40 agree, 0 diverge.

## Rule coverage and book Comments

| Program | Label | Implementation (CHECK) | Definition | Status |
|---|---|---|---|---|
| StandardCoreEvaluationExamplesTest | as-pattern | (1,[1,2]) | (1,[1,2]) | agree |
| StandardCoreEvaluationExamplesTest | unit pattern | 5 | 5 | agree |
| StandardCoreEvaluationExamplesTest | operator value | 3 | 3 | agree |
| StandardCoreEvaluationExamplesTest | partial basic value | <function> | <function> | agree |
| StandardCoreEvaluationExamplesTest | partial constructor | <function> | <function> | agree |
| StandardCoreEvaluationExamplesTest | (&&) is strict | False | False | agree |
| StandardCoreEvaluationExamplesTest | pipe | 6 | 6 | agree |
| StandardCoreEvaluationExamplesTest | mrule-fail | 2 | 2 | agree |
| StandardCoreEvaluationExamplesTest | Just 1 | Just 1 | Just 1 | agree |
| StandardCoreEvaluationExamplesTest | inc 0.5 | 1.5 | 1.5 | agree |
| StandardCoreEvaluationExamplesTest | modBy 4 -5 | 3 | 3 | agree |
| StandardCoreEvaluationExamplesTest | remainderBy 4 -5 | -1 | -1 | agree |
| StandardCoreEvaluationExamplesTest | record field order | True | True | agree |
| StandardCoreEvaluationExamplesTest | compare strings | LT | LT | agree |
| StandardCoreEvaluationExamplesTest | accessor | 7 | 7 | agree |
| StandardLetStrictTest | before | () | () | agree |
| StandardLetStrictTest | let strict | (no value) | (no value) | agree |
| StandardApplicationStrictTest | before | () | () | agree |
| StandardApplicationStrictTest | app strict | (no value) | (no value) | agree |

Rule coverage and book Comments: 19 checks, 19 agree, 0 diverge.

Total: 208 checks, 208 agree, 0 diverge.
