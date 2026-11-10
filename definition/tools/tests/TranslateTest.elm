module TranslateTest exposing (suite)

{-| The translator, end to end on small programs: refusal reasons, inference of literal types,
number specialisation, printing (plans/elm-to-lean-translator.md, B.2 to B.9).
-}

import Expect exposing (Expectation)
import Test exposing (Test, describe, test)
import Translate.Directives as Directives
import Translate.Literal as Literal
import Translate.Pipeline as Pipeline exposing (Outcome(..))


{-| A test program with the given declarations before `main`, the given checks (label, expression,
expected) and extra directive lines.
-}
program : { imports : String, directives : String, decls : String, checks : List ( String, String, String ) } -> String
program p =
    "module T exposing (main)\n\n"
        ++ p.directives
        ++ "-- TAGS: elm-spec\n"
        ++ String.concat (List.map (\( l, _, v ) -> "-- CHECK: " ++ l ++ ": " ++ v ++ "\n") p.checks)
        ++ "\nimport Html exposing (text)\n"
        ++ p.imports
        ++ "\n\n"
        ++ p.decls
        ++ "\n\nmain =\n    let\n"
        ++ String.concat (List.map (\( l, e, _ ) -> "        _ =\n            Debug.log \"" ++ l ++ "\" (" ++ e ++ ")\n\n") p.checks)
        ++ "    in\n    text \"done\"\n"


simple : String -> List ( String, String, String ) -> String
simple decls checks =
    program { imports = "", directives = "", decls = decls, checks = checks }


run : String -> Outcome
run source =
    Pipeline.translate { project = "elm", name = "T", defName = "g" } source (Directives.read source)


refusedWith : String -> String -> Expectation
refusedWith reason source =
    case run source of
        Refused r ->
            Expect.equal reason r.reason

        Translated t ->
            Expect.fail ("translated:\n" ++ t.lean)


translatedContaining : List String -> String -> Expectation
translatedContaining fragments source =
    case run source of
        Translated t ->
            Expect.all (List.map (\f -> \lean -> (if String.contains f lean then Expect.pass else Expect.fail ("expected `" ++ f ++ "` in:\n" ++ lean))) fragments) t.lean

        Refused r ->
            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)


suite : Test
suite =
    describe "The translator"
        [ describe "refusals"
            [ test "a compile-error test" <|
                \_ -> refusedWith "compile-error" (program { imports = "", directives = "-- COMPILE-ERROR: TYPE MISMATCH\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a flag directive" <|
                \_ -> refusedWith "effects" (program { imports = "", directives = "-- FLAGS: 1\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "CHECK-NEXT" <|
                \_ -> refusedWith "checks:directive:CHECK-NEXT" (program { imports = "", directives = "-- CHECK-NEXT: y\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "an unlabelled CHECK line" <|
                \_ -> refusedWith "checks:unlabelled" (program { imports = "", directives = "-- CHECK: person\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a regular expression in a CHECK line" <|
                \_ -> refusedWith "checks:regex" (program { imports = "", directives = "-- CHECK: y: {{.*}}\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "an import outside the fragment" <|
                \_ -> refusedWith "import:Dict" (program { imports = "import Dict\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a restated default import is accepted" <|
                \_ -> translatedContaining [ "ckk \"x\" \"1\" .int (i 1)" ] (program { imports = "import Basics exposing (..)\nimport Maybe exposing (Maybe(..))\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a use of an effect module" <|
                \_ -> refusedWith "effects" (program { imports = "import Task\n", directives = "", decls = "t = Task.succeed 1", checks = [ ( "x", "1", "1" ) ] })
            , test "a value of the basis the encoding does not include" <|
                \_ -> refusedWith "basis:String.fromInt" (simple "" [ ( "x", "String.fromInt 1", "\"1\"" ) ])
            , test "a library function outside the book's basis" <|
                \_ -> refusedWith "basis:Tuple.first" (simple "" [ ( "x", "Tuple.first ( 1, 2 )", "1" ) ])
            , test "a record alias used as a constructor" <|
                \_ -> refusedWith "construct:record-alias-constructor" (simple "type alias P = { x : Int }" [ ( "x", "(P 1).x", "1" ) ])
            , test "a check whose CHECK line is missing" <|
                \_ ->
                    refusedWith "checks:unmatched:y"
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html exposing (text)\nmain =\n    let\n        _ = Debug.log \"x\" 1\n        _ = Debug.log \"y\" 2\n    in\n    text \"done\"\n")
            , test "a main that is not a let" <|
                \_ -> refusedWith "construct:main-shape" "module T exposing (main)\n-- TAGS: elm-spec\nimport Html exposing (text)\nmain = text \"done\"\n"
            , test "a CHECK-NOT line without EXIT 1" <|
                \_ -> refusedWith "checks:check-not" (program { imports = "", directives = "-- CHECK-NOT: y:\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "an exit status other than 0, or 1 with a CHECK-NOT" <|
                \_ -> refusedWith "checks:exit" (program { imports = "", directives = "-- EXIT: 2\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a check logged by a pipe" <|
                \_ ->
                    refusedWith "construct:check-shape"
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html exposing (text)\nmain =\n    let\n        _ = 1 |> Debug.log \"x\"\n    in\n    text \"done\"\n")
            , test "a record pattern binding needed at Float (its variables are the fields, so they cannot be renamed for a copy)" <|
                \_ -> refusedWith "number" (simple "" [ ( "x", "let { a } = { a = 1 } in a / 2", "0.5" ) ])
            , test "a program that does not type" <|
                \_ -> refusedWith "type" (simple "" [ ( "x", "1 + \"a\"", "1" ) ])
            , test "a program too large" <|
                \_ -> refusedWith "construct:large-program" (simple ("big = 0\n" ++ String.repeat 2000 "-- padding padding\n") [ ( "x", "big", "0" ) ])
            ]
        , describe "inference of literal types"
            [ test "a literal under / is Float" <|
                \_ -> translatedContaining [ "bin \"/\" (.atexp (.scon (.intF 1))) (.atexp (.scon (.intF 2)))" ] (simple "" [ ( "x", "1 / 2", "0.5" ) ])
            , test "a literal under // is Int" <|
                \_ -> translatedContaining [ "bin \"//\" (i 7) (i 2)" ] (simple "" [ ( "x", "7 // 2", "3" ) ])
            , test "a literal alone is Int by default" <|
                \_ -> translatedContaining [ "ckk \"x\" \"3\" .int (bin \"+\" (i 1) (i 2))" ] (simple "" [ ( "x", "1 + 2", "3" ) ])
            , test "through a record field" <|
                \_ -> translatedContaining [ "recE [(\"a\", .atexp (.scon (.intF 1)))]" ] (simple "r = { a = 1 }" [ ( "x", "r.a / 2", "0.5" ) ])
            , test "through Maybe and a case" <|
                \_ -> translatedContaining [ ".atexp (.scon (.intF 2))" ] (simple "m = Just 2" [ ( "x", "case m of\n                Just y -> y / 4\n                Nothing -> 0", "0.5" ) ])
            , test "through a lambda" <|
                \_ -> translatedContaining [ "lams [pv \"z\"] (bin \"+\" (v \"z\") (.atexp (.scon (.intF 1))))" ] (simple "" [ ( "x", "(\\z -> z + 1) 0.5", "1.5" ) ])
            , test "a hex literal is exact" <|
                \_ -> translatedContaining [ "i 18446744073709551615" ] (simple "" [ ( "x", "0xFFFFFFFFFFFFFFFF", "-1" ) ])
            , test "a literal after an astral character on its line" <|
                \_ -> translatedContaining [ "ckk \"x\" \"( '😀', 12 )\" .data (tup2 (.atexp (chA '😀')) (i 12))" ] (simple "" [ ( "x", "( '😀', 12 )", "( '😀', 12 )" ) ])
            , test "a negative literal is a negation" <|
                \_ -> translatedContaining [ ".atexp (neg (A (i 7)))" ] (simple "" [ ( "x", "-7", "-7" ) ])
            ]
        , describe "number specialisation"
            [ test "a declaration used at Int and Float gets two copies" <|
                \_ ->
                    translatedContaining [ ".fn \"inc\" [pv \"n\"] (bin \"+\" (v \"n\") (i 1))", ".fn \"inc$Float\" [pv \"n\"] (bin \"+\" (v \"n\") (.atexp (.scon (.intF 1))))", "ap (v \"inc$Float\")", "ap (v \"inc\") [i 1]" ]
                        (simple "inc n = n + 1" [ ( "x", "inc 0.5", "1.5" ), ( "y", "inc 1", "2" ) ])
            , test "an unused declaration keeps its default copy" <|
                \_ -> translatedContaining [ ".fn \"unused\" [pv \"n\"] (bin \"*\" (v \"n\") (i 2))" ] (simple "unused n = n * 2" [ ( "x", "1", "1" ) ])
            , test "an annotated number function" <|
                \_ ->
                    translatedContaining [ ".fn \"twice$Float\"" ]
                        (simple "twice : number -> number\ntwice n = n * 2" [ ( "x", "twice 1.5", "3" ) ])
            , test "a pattern binding used at Float is copied, every variable renamed (one word per number variable: a, then b)" <|
                \_ -> translatedContaining [ ".pat (ptup2 (P (pv \"a$Float$Int\")) (P (pv \"b$Float$Int\")))", "v \"a$Float$Int\"" ] (simple "" [ ( "x", "let ( a, b ) = ( 1, 2 ) in a / 2", "0.5" ) ])
            , test "isNaN and isInfinite are values of E0" <|
                \_ -> translatedContaining [ "ap (v \"isNaN\")", "ap (v \"isInfinite\")" ] (simple "" [ ( "x", "isNaN (0 / 0)", "True" ), ( "y", "isInfinite (1 / 0)", "True" ) ])
            , test "++ is the operator of append, at String and at List" <|
                \_ -> translatedContaining [ "bin \"++\" (str \"a\") (str \"b\")", "bin \"++\" (listE [i 1]) (listE [i 2])" ] (simple "" [ ( "x", "\"a\" ++ \"b\"", "\"ab\"" ), ( "y", "[ 1 ] ++ [ 2 ]", "[1,2]" ) ])
            , test "the conversions: a program that uses round is checked natively" <|
                \_ -> translatedContaining [ "native := true", "ap (v \"round\")", "ap (v \"toFloat\") [i 2]" ] (simple "" [ ( "x", "round 1.5", "2" ), ( "y", "toFloat 2", "2" ) ])
            , test "toFloat and sqrt alone are computed by the kernel" <|
                \_ -> translatedContaining [ "def g : Program := {\n  name := \"T\", source := \"tests/elm/src\",\n" ] (simple "" [ ( "x", "sqrt (toFloat 4)", "2" ) ])
            , test "^ at Float is ^, its program checked natively" <|
                \_ -> translatedContaining [ "native := true", "bin \"^\" (.atexp (.scon (.float 20 (-1))))" ] (simple "" [ ( "x", "2.0 ^ 2", "4" ) ])
            , test "^ at Int stays with the kernel" <|
                \_ -> translatedContaining [ "def g : Program := {\n  name := \"T\", source := \"tests/elm/src\",\n", "bin \"^\" (i 2) (i 3)" ] (simple "" [ ( "x", "2 ^ 3", "8" ) ])
            , test "Char.toCode, Char.fromCode and Debug.toString are qualified values of E0" <|
                \_ -> translatedContaining [ "qv \"Char\" \"toCode\"", "qv \"Char\" \"fromCode\"", "qv \"Debug\" \"toString\"", "native := true" ] (simple "" [ ( "x", "Char.toCode 'a'", "97" ), ( "y", "Char.fromCode 98", "'b'" ), ( "z", "Debug.toString 1", "\"1\"" ) ])
            , test "abs at Float is its copy at Float" <|
                \_ -> translatedContaining [ "v \"abs$Float\"" ] (simple "" [ ( "x", "abs -1.5", "1.5" ) ])
            , test "ruling A93: a group's number variable a use does not fix is Int" <|
                \_ ->
                    translatedContaining [ "bin \"^\" (ap (v \"g\") [i 1" ]
                        (simple "f n =\n    if n <= 0 then 0 else if g 1 (n - 1) ^ -1 > 0 then 1 else 0\n\ng y k =\n    if k <= 0 then y + 1 else let _ = f k in y + 1" [ ( "f 3", "f 3", "0" ) ])
            ]
        , describe "literals"
            [ test "hex to decimal" <|
                \_ -> Literal.decimalOfHex "0xFF" |> Expect.equal "255"
            , test "a float's mantissa and exponent" <|
                \_ -> Literal.floatOf "1.50e3" |> Expect.equal (Just { mantissa = "150", exponent = 1 })
            , test "a Lean string with escapes" <|
                \_ -> Literal.leanString "a\"b\\c\n" |> Expect.equal "\"a\\\"b\\\\c\\n\""
            ]
        ]
