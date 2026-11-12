module Translate.ClassifyOverrides exposing (Override, overrides)

{-| The one hand edit surface of the static classification (plans/lean-full-definition/
step-07-classify.md, section 2.4): tests whose automatic class is `inference` but which step 9
refuses without inference (`static-deterministic`, with the family of P2-13), or whose first tag is
not the restriction they break. Each entry carries a note for the reader of the JSON. Reviewed
2026-11-11 from each test's source, its `-- COMPILE-ERROR:` text and its tags; a later step that
cannot prove a test in its class changes its entry here and says so in its report.
-}


type alias Override =
    { name : String
    , rule : Maybe String
    , class : String
    , subclass : Maybe String
    , note : String
    }


overrides : List Override
overrides =
    [ { name = "NamingErrorAnUnknownVariableTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "scope"
      , note = "a name that no environment of any derivation binds"
      }
    , { name = "CompilerIssue1550RecordExtensionDuplicateFieldTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue1785ExtensibleAliasOfUnitTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue1896ExtendCustomTypeCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue1952ExtendIntCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2064ExtendStringNotEnoughBytesTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2072ExtendUnitInResultCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2083ExtendCustomTypeFieldAccessCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2097ExtensibleUnitArgCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2176ExtensibleUnitAliasCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2182ExtensibleFunctionAliasCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "QualifiedTypeNotExposedTest"
      , rule = Just "res:modules-value-recursion"
      , class = "syntactic"
      , subclass = Nothing
      , note = "besides the type List.Bar (r:s-ty-con), its foo = foo refers to itself directly, which res:modules-value-recursion forbids on the tree (step 8)"
      }
    , { name = "TypeConstructorTooFewArgsTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "a type expression that elaborates in no context the rules can build (r:s-ty-con)"
      }
    , { name = "CompilerIssue2200ConstrainedExtensibleErrorCrashTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "type-expression"
      , note = "an open record type whose row variable has a constrained class, which no context admits (r:s-ty-openrecord)"
      }
    , { name = "ImportAliasOpenItemTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "module"
      , note = "imports, exposing, a port's payload type or the names of ports, decided without inference"
      }
    , { name = "ImportClosedTypeConstructorTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "module"
      , note = "imports, exposing, a port's payload type or the names of ports, decided without inference"
      }
    , { name = "ImportUnexposedValueTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "module"
      , note = "imports, exposing, a port's payload type or the names of ports, decided without inference"
      }
    , { name = "ImportUnknownOperatorTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "module"
      , note = "imports, exposing, a port's payload type or the names of ports, decided without inference"
      }
    , { name = "PortProblemCharPayloadTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "module"
      , note = "imports, exposing, a port's payload type or the names of ports, decided without inference"
      }
    , { name = "StandardA84DuplicatePortNameTest"
      , rule = Just "res:modules-program"
      , class = "syntactic"
      , subclass = Nothing
      , note = "two modules declare ports of one name, which res:modules-program forbids on the tree (step 8)"
      }
    , { name = "BadMainTypeAliasMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "the type of main is fixed by its annotation, and is not that of a view or a program"
      }
    , { name = "BadMainTypeFunctionMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "the type of main is fixed by its annotation, and is not that of a view or a program"
      }
    , { name = "BadMainTypeRecordMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "the type of main is fixed by its annotation, and is not that of a view or a program"
      }
    , { name = "BadMainTypeThreeArgumentTypeMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "the type of main is fixed by its annotation, and is not that of a view or a program"
      }
    , { name = "BadMainTypeUnitMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "the type of main is fixed by its annotation, and is not that of a view or a program"
      }
    , { name = "BadMainTypeTypeVariableMainTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "main = [] has head List in every derivation, so main is neither a view nor a program"
      }
    , { name = "TooFewArgsAConstructorPatternWithTooFewArgumentsTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "arity"
      , note = "a constructor pattern with the wrong number of arguments"
      }
    , { name = "TooManyArgsAConstructorPatternWithTooManyArgumentsTest"
      , rule = Nothing
      , class = "static-deterministic"
      , subclass = Just "arity"
      , note = "a constructor pattern with the wrong number of arguments"
      }
    , { name = "BadMainRecursiveMainTest"
      , rule = Just "r:p-stat-main-program"
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "main reaches itself only through f, which res:program-main allows (main does not occur free in its own expression); main : Int -> Int is neither a view nor a program"
      }
    , { name = "BadMainRecursiveUnannotatedMainTest"
      , rule = Just "r:p-stat-main-program"
      , class = "static-deterministic"
      , subclass = Just "main"
      , note = "main reaches itself only through f, which res:program-main allows; main x = ... has a function type in every derivation, neither a view nor a program"
      }
    ]
