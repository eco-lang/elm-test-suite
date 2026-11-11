# Compile-error tests (batch ce2): check against the book

155 tests, all expected to be refused. Verdicts: OK 155, WRONG 0, TAG 0, UNSURE 0.

| Test | Verdict | Refusing rule / restriction | Note |
|---|---|---|---|
| TypeMismatchCompappendAgainstATupleTest | OK | s-exp-app (via df:list, s-atexp-op ::) | first components: integer constant (Adm(number)) against String; no derivation; tags: s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchCompappendListEntryWithABoolTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchComparableAgainstATupleTest | OK | s-exp-app (via df:list, s-atexp-op ::) | first components 1 against "s"; no derivation; tags: s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchComposedWithANumberTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchConsHeadAgainstAConsTailTest | OK | s-pat-cons, s-atpat-scon | 1 elaborates at Int only, "s" at String; list elements must agree; tags: s-pat-cons, s-atpat-scon |
| TypeMismatchConsedOntoABoolTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchConsedOntoAMaybeTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchConstructorPatternTest | OK | s-exp-case, s-pat-con | scrutinee type in Adm(number), pattern type Maybe; tags: s-exp-case, s-pat-con, s-atexp-scon |
| TypeMismatchDestructureTest | OK | s-valbind-pat, s-atpat-tuple | tuple pattern against integer constant (Adm(number) has no tuple); tags: s-valbind-pat, s-atpat-tuple |
| TypeMismatchDifferentlyNamedComparableVarsTest | OK | s-exp-app (df:list) | A against B in the tuples; tags: sm-datbind, s-atexp-tuple, s-exp-app, s-atexp-longvar |
| TypeMismatchDifferentlyNamedFlexVarsTest | OK | s-exp-app (df:list) | A against B in the tuples; tags: sm-datbind, s-atexp-tuple, s-exp-app, s-atexp-longvar |
| TypeMismatchExtensibleRecordGivenAClosedOneTest | OK | s-valbind-var | closed {name:Int} against open record with explicit row variable r; tags: s-valbind-var, s-ty-openrecord, s-atexp-record |
| TypeMismatchExtensibleRecordMissingAFieldTest | OK | s-exp-app | {age:Int} closed has no name field; tags: s-exp-app, s-atexp-record |
| TypeMismatchFieldAccessUnderIntTest | OK | s-valbind-var / s-atpat-record (df:field-selection) | r.name is String, annotation Int; tags: s-valbind-var, s-atpat-record |
| TypeMismatchFieldTypoTest | OK | s-atpat-record, s-exp-app (df:field-selection) | closed {name} lacks nmae; tags: s-atpat-record, s-exp-app |
| TypeMismatchFlexibleRecordWhereClosedAfterAMismatchTest | OK | s-exp-app | "s" against Int (and name String against Int); tags: s-exp-app, s-atexp-tuple, s-atpat-record |
| TypeMismatchFlexibleRecordWithAnExtraFieldWhereClosedTest | OK | s-atpat-record, s-exp-app | a must have age, closed {name:Int} has none; tags: s-atpat-record, s-exp-app |
| TypeMismatchFloatComparedForEqualityTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatLeftOfAppendTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatLeftOfIntDivideTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app, s-atexp-scon |
| TypeMismatchFloatRightOfIntDivideTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app, s-atexp-scon |
| TypeMismatchFloatRightOfMinusWithIntTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatRightOfPlusWithIntTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatRightOfPowerWithIntTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatRightOfTimesWithIntTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchFloatUnderIntTest | OK | s-valbind-var, s-atexp-scon | 1.5 is Float only; tags: s-valbind-var, s-atexp-scon |
| TypeMismatchFunctionInATypeArgumentTest | OK | s-valbind-var | List against Maybe; tags: s-valbind-var, s-ty-con, s-ty-fun |
| TypeMismatchFunctionLeftOfGreaterThanTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIfBranchTest | OK | s-match (df:if) | branches number against String; tags: s-match |
| TypeMismatchIfConditionIntTest | OK | s-exp-case, s-atpat-con (df:if) | Basics.True pattern is Bool, scrutinee in Adm(number); tags: s-exp-case, s-atpat-con, s-atexp-scon |
| TypeMismatchIfUnderIntTest | OK | s-valbind-var | String against Int; tags: s-valbind-var |
| TypeMismatchImportedTypeNamedLikeAnAliasTest | OK | s-exp-app (df:list) | Basics.True is Bool of the basis, b is local alias Bool = Int; local declaration may replace the imported name (sm-topdec-seq); tags: sm-typbind, sm-topdec-seq, s-ty-con, s-exp-app |
| TypeMismatchIntAgainstNumberAfterAMismatchTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfAppendTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfAppendWithAListTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfDivideTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfMinusWithFloatTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfPlusWithFloatTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfPowerWithFloatTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntRightOfTimesWithFloatTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchIntWhereFloatTest | OK | s-valbind-var | Int against Float; tags: s-valbind-var |
| TypeMismatchLambdaArgumentPatternTest | OK | s-exp-app, s-atpat-tuple | tuple against Adm(number); tags: s-exp-app, s-exp-lambda, s-atpat-tuple |
| TypeMismatchLambdaCallAsAnArgumentTest | OK | s-exp-app | number against Bool; tags: s-exp-app, s-exp-lambda |
| TypeMismatchListConsedOntoAListOfStringsTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchListEntryPatternTest | OK | s-pat-cons, s-atpat-scon (df:list-pattern) | Int against String elements; tags: s-pat-cons, s-atpat-scon |
| TypeMismatchListMultipliedTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchListPatternTest | OK | s-exp-case, s-atpat-nil | List against Adm(number); tags: s-exp-case, s-atpat-nil, s-atexp-scon |
| TypeMismatchListRightOfAppendWithAStringTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchListRightOfPlusTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchListRightOfTimesTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchListsAddedTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchLocalTypeNamedLikeAnImportedOneTest | OK | s-valbind-var | local Maybe Int against basis Maybe (Maybe.Just via default import); tags: sm-datbind, sm-topdec-seq, s-ty-con, s-valbind-var |
| TypeMismatchMaybeConsedOntoAListOfStringsTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchMaybeOfANumberAgainstARigidVarTest | OK | s-valbind-var | explicit a against Maybe; tags: s-valbind-var, s-atexp-longcon |
| TypeMismatchMisspeltFieldAmongManyTest | OK | s-atpat-record, s-exp-app (df:field-selection) | closed record lacks alpah; tags: s-atpat-record, s-exp-app |
| TypeMismatchMisspeltFieldOfExtensibleRecordTest | OK | s-atpat-record, s-valbind-var | explicit row variable a; alpah not among fields; tags: s-atpat-record, s-valbind-var, s-ty-openrecord |
| TypeMismatchNegateTest | OK | s-exp-app (df:negation, Basics.negate) | String not in Adm(number); tags: s-exp-app |
| TypeMismatchNumberAndAppendableListEntriesTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberAndCompappendListEntriesTest | OK | s-exp-app | number and compappend have no common subclass; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberIntoNotWithPipeLeftTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberLeftOfAndTest | OK | s-exp-case, s-atpat-con (df:and, df:if) | Bool pattern against Adm(number); tags: s-exp-case, s-atpat-con, s-atexp-scon |
| TypeMismatchNumberLeftOfComposeRightTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberLeftOfOrTest | OK | s-exp-case, s-atpat-con (df:or, df:if) | Bool pattern against Adm(number); tags: s-exp-case, s-atpat-con, s-atexp-scon |
| TypeMismatchNumberLeftOfPipeLeftTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberListEntryWithAnAliasTest | OK | s-exp-app (df:list, s-atexp-op ::) | record against Adm(number); tags: s-atexp-op, s-exp-app, s-atexp-scon |
| TypeMismatchNumberPipedIntoANumberTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberPipedIntoNotTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberPlusAppendableTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchNumberRightOfAndTest | OK | s-match (df:and, df:if) | branch number against Basics.False; tags: s-exp-case, s-match |
| TypeMismatchNumberRightOfOrTest | OK | s-match (df:or, df:if) | branch Basics.True against number; tags: s-exp-case, s-match |
| TypeMismatchOneArgumentFunctionWhereTwoTest | OK | s-valbind-var | Int -> Int against Int -> Int -> Int; tags: s-valbind-var, s-ty-fun |
| TypeMismatchParameterisedAliasTest | OK | s-valbind-var | {v:Int} against {v:String}; tags: sm-typbind-record, s-ty-con, s-valbind-var |
| TypeMismatchRecordFieldExtraTest | OK | s-exp-app | closed record types differ; tags: s-exp-app, s-atexp-record |
| TypeMismatchRecordFieldsMissingTest | OK | s-exp-app | closed record types differ; tags: s-exp-app, s-atexp-record |
| TypeMismatchRecordLeftOfAtMostTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchRecordPatternTest | OK | s-atpat-record, s-valbind-var | record pattern needs a record type, annotation Int; tags: s-valbind-var, s-atpat-record |
| TypeMismatchRecordWhereEmptyClosedRecordTest | OK | s-valbind-var | {a} against {}; tags: s-valbind-var, s-ty-record, s-atexp-record |
| TypeMismatchRigidAppendableAddedTest | OK | s-valbind-var, s-atexp-op | explicit appendable variable not in Adm(number); tags: s-valbind-var, s-atexp-op |
| TypeMismatchRigidCompappendAsIntTest | OK | s-valbind-var | explicit compappend against Int; tags: s-valbind-var |
| TypeMismatchRigidComparableAsANumberTest | OK | s-valbind-var, s-atexp-scon | explicit comparable variable not in Adm(number); tags: s-valbind-var, s-atexp-scon |
| TypeMismatchRigidComparableAsNumberTest | OK | s-valbind-var | two explicit variables; tags: s-valbind-var |
| TypeMismatchRigidExtensionWhereClosedTest | OK | s-valbind-var | open record with explicit row variable against closed; tags: s-valbind-var, s-ty-openrecord |
| TypeMismatchRigidExtensionWhereFlexibleAfterAMismatchTest | OK | s-exp-app (df:list) | 1 against "s" in first components; tags: s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchRigidNumberAsAliasTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var |
| TypeMismatchRigidNumberAsFunctionTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-exp-lambda |
| TypeMismatchRigidNumberAsMaybeTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-longcon |
| TypeMismatchRigidNumberAsRecordTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-record |
| TypeMismatchRigidNumberAsRigidVarTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var |
| TypeMismatchRigidNumberAsTupleTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-tuple |
| TypeMismatchRigidNumberAsUnitTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-unit |
| TypeMismatchRigidVarAgainstItsListTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-ty-con |
| TypeMismatchRigidVarAgainstItsMaybeTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-ty-con |
| TypeMismatchRigidVarAppendedTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-op |
| TypeMismatchRigidVarAsAliasTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var |
| TypeMismatchRigidVarAsFunctionTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-exp-lambda |
| TypeMismatchRigidVarAsMaybeTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-longcon |
| TypeMismatchRigidVarAsRecordTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-record |
| TypeMismatchRigidVarAsRigidNumberTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var |
| TypeMismatchRigidVarAsTupleTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-tuple |
| TypeMismatchRigidVarAsUnitTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-unit |
| TypeMismatchRigidVarComparedTest | OK | s-valbind-var | body type differs from the annotation (explicit variables uninstantiated); tags: s-valbind-var, s-atexp-op |
| TypeMismatchSameRigidExtensionTest | OK | s-valbind-var | name Int against String; tags: s-valbind-var, s-ty-openrecord |
| TypeMismatchSecondArgumentToAFunctionTest | OK | s-exp-app | integer constant against String; tags: s-exp-app |
| TypeMismatchSecondCasePatternTest | OK | s-match, s-atpat-scon | Char pattern against String; tags: s-match, s-atpat-scon |
| TypeMismatchSelfAppliedArgumentAgainstANumberTest | OK | s-exp-app | x x: types are finite (no tau = tau -> tau'); tags: s-exp-app, s-exp-lambda |
| TypeMismatchSelfAppliedArgumentAgainstARigidNumberTest | OK | s-exp-app | x x: types are finite; tags: s-exp-app, s-exp-lambda, s-valbind-var |
| TypeMismatchSelfAppliedArgumentAgainstARigidVarTest | OK | s-exp-app | x x: types are finite; tags: s-exp-app, s-exp-lambda, s-valbind-var |
| TypeMismatchStringAppendedToListTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringLeftOfConsTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringLeftOfDivideTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringLeftOfIntDivideTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringLeftOfLessThanTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringLeftOfPlusTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfAtLeastTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfAtMostTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfGreaterThanTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfMinusTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfNotEqualsTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfPlusTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfPowerTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchStringRightOfTimesTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchTailPatternTest | OK | s-pat-cons, s-atpat-scon | String where a list pattern is needed; tags: s-pat-cons, s-atpat-scon |
| TypeMismatchThirdCaseBranchTest | OK | s-match | branches String against number; tags: s-match |
| TypeMismatchTriplesDifferTest | OK | s-valbind-var | third component String against Int; tags: s-valbind-var, s-atexp-tuple, s-ty-tuple |
| TypeMismatchTupleAgainstAnAliasTest | OK | s-exp-app (df:list) | Int against pair; tags: sm-typbind, s-ty-con, s-atexp-op, s-exp-app |
| TypeMismatchTupleComponentPatternTest | OK | s-exp-case, s-atpat-scon | String pattern against Adm(number); tags: s-exp-case, s-atpat-tuple, s-atpat-scon |
| TypeMismatchTupleSizesDifferTest | OK | s-valbind-var | triple against pair; tags: s-valbind-var, s-atexp-tuple, s-ty-tuple |
| TypeMismatchTwentyEightTypeVariablesTest | OK | s-exp-app (s-atexp-op +) | function type not in Adm(number); tags: s-atexp-op, s-exp-app |
| TypeMismatchTwoAliasedRecordsTest | OK | s-valbind-var | {a} against {b}; tags: sm-typbind-record, s-ty-con, s-valbind-var |
| TypeMismatchTwoArgumentLambdaWhereOneTest | OK | s-valbind-var (df:lambda-params) | function against Int; tags: s-valbind-var, s-exp-lambda |
| TypeMismatchTwoComparableVarsTest | OK | s-exp-app (df:list) | A against B; tags: sm-datbind, s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchTwoExtensibleRecordsTest | OK | s-valbind-var | distinct explicit row variables; tags: s-valbind-var, s-ty-openrecord |
| TypeMismatchTwoFlexibleRecordsTest | OK | s-exp-app | name number against String; tags: s-atpat-record, s-exp-app |
| TypeMismatchTwoRigidVarsTest | OK | s-valbind-var | two explicit variables; tags: s-valbind-var |
| TypeMismatchTypeUnderAnExposingListTest | OK | s-valbind-var | Maybe against Int. Side note: Tuple and List have empty interfaces in ME0, so importing first, pair, map also fails (sm-item-var); the tagged reason still holds; tags: s-valbind-var, s-atexp-longcon |
| TypeMismatchTypeWhereAnAliasTest | OK | s-valbind-var | String against alias of Int; tags: sm-typbind, s-ty-con, s-valbind-var |
| TypeMismatchUnitLeftOfAtLeastTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-op, s-exp-app |
| TypeMismatchUnitPatternTest | OK | s-valbind-var, s-atpat-unit | unit pattern against Int; tags: s-valbind-var, s-atpat-unit |
| TypeMismatchUnitsOnBothSidesTest | OK | s-exp-app (s-atexp-op gives the operator scheme; df:infix) | operand type is no instance of the operator scheme; tags: s-atexp-tuple, s-atexp-op, s-exp-app |
| TypeMismatchUnknownTypeAgainstANumberTest | OK | s-exp-app (df:list in scrutinee), s-match | [1, "a"] already has no derivation; tags: s-atexp-op, s-exp-app, s-match |
| TypeMismatchUnknownTypeAgainstARigidNumberTest | OK | s-exp-app (df:list in scrutinee) | [1, "a"] already has no derivation; tags: s-atexp-op, s-exp-app, s-match, s-valbind-var |
| TypeMismatchUnknownTypeAgainstARigidVarTest | OK | s-exp-app (df:list in scrutinee) | [1, "a"] already has no derivation; tags: s-atexp-op, s-exp-app, s-match, s-valbind-var |
| TypeMismatchUnknownTypesOnBothSidesTest | OK | s-exp-app (df:list) | [1, "a"] already has no derivation; tags: s-atexp-op, s-exp-app, s-atexp-tuple |
| TypeMismatchUpdateOfANearFieldTest | OK | s-atexp-update | cuont not in the row of {count}; tags: s-atexp-update |
| TypeMismatchUpdateOfANumberTest | OK | s-atexp-update | Int not in RecType; tags: s-atexp-update |
| TypeMismatchUpdateOfAnEmptyRecordTest | OK | s-atexp-update | x not in the row of {}; tags: s-atexp-update |
| TypeMismatchUpdateValueTest | OK | s-atexp-update | x at String against Int; tags: s-atexp-update |
| TypeParameterTwiceTest | OK | modules-tyvarseq-distinct | Pair a a (Html.text is also not in ME0(Html), but the restriction refuses first); tags: modules-tyvarseq-distinct |
| UnexpectedPatternFloatWithExponentTest | OK | core-no-float-pattern | 1e3 is a float constant; tags: core-no-float-pattern |
| UnknownOperatorAnUnknownOperatorTest | OK | s-atexp-op (df:infix) | <=> is an operator lexically but not in Dom OTstat; tags: s-atexp-op |
| UnsafePatternAllDestructPatternsEdgeCaseCasesTest | OK | core-exhaustiveness | (h :: t) does not cover []; tags: core-exhaustiveness |
| UnsafePatternDestructFixedListPatternLetDestructCasesTest | OK | core-exhaustiveness | [a, b] does not cover [] (df:list-pattern); tags: core-exhaustiveness |
| UnsafePatternMixedNestedAliasesAsPatternCasesTest | OK | core-exhaustiveness | parameter pattern; h :: _ does not cover []; tags: core-exhaustiveness |
| UnsafePatternTripleNestedPatternsPatternArgCasesTest | OK | core-exhaustiveness | parameter pattern; h :: t does not cover []; tags: core-exhaustiveness |
| WeirdElseBranchElseNotIndentedTest | OK | core-layout-rule | else at the let indentation d, not indented; tags: core-layout-rule |
