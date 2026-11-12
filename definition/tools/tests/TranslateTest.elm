module TranslateTest exposing (suite)

{-| The translator, end to end on small programs: refusal reasons, inference of literal types,
number specialisation, printing (plans/elm-to-lean-translator.md, B.2 to B.9).
-}

import Expect exposing (Expectation)
import Test exposing (Test, describe, test)
import Translate.Directives as Directives
import Translate.Choices as Choices
import Translate.Json as Json
import Json.Decode as Decode
import Dict
import Translate.Literal as Literal
import Translate.Pipeline as Pipeline exposing (Outcome(..))


{-| A test with helper modules: their names and texts.
-}
runWith : List ( String, String ) -> String -> Outcome
runWith helpers source =
    let
        lookup name =
            helpers
                |> List.filter (\( n, _ ) -> n == name)
                |> List.head
                |> Maybe.map (\( n, text ) -> { path = "tests/elm/src/" ++ n ++ ".elm", source = text })
    in
    Pipeline.translateWith lookup { project = "elm", name = "T", defName = "g" } source (Directives.read source)


withHelpers : List ( String, String ) -> List String -> String -> Expectation
withHelpers helpers fragments source =
    case runWith helpers source of
        Translated t ->
            Expect.all (List.map (\f -> \lean -> (if String.contains f lean then Expect.pass else Expect.fail ("expected `" ++ f ++ "` in:\n" ++ lean))) fragments) t.lean

        Refused r ->
            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)


refusedWithHelpers : List ( String, String ) -> String -> String -> Expectation
refusedWithHelpers helpers reason source =
    case runWith helpers source of
        Refused r ->
            Expect.equal reason r.reason

        Translated t ->
            Expect.fail ("translated:\n" ++ t.lean)


{-| A main module importing the given lines, logging `x` with the given expression.
-}
mainWith : String -> String -> String -> String
mainWith imports checkLine e =
    "module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: " ++ checkLine ++ "\nimport Html exposing (text)\n" ++ imports ++ "\nmain =\n    let\n        _ = Debug.log \"x\" (" ++ e ++ ")\n    in\n    text \"done\"\n"


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


translatedLackingAnd : List String -> List String -> String -> Expectation
translatedLackingAnd absent present source =
    case run source of
        Translated t ->
            Expect.all
                (List.map (\f -> \lean -> (if String.contains f lean then Expect.fail ("did not expect `" ++ f ++ "` in:\n" ++ lean) else Expect.pass)) absent
                    ++ List.map (\f -> \lean -> (if String.contains f lean then Expect.pass else Expect.fail ("expected `" ++ f ++ "` in:\n" ++ lean))) present
                )
                t.lean

        Refused r ->
            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)


allReasons : String -> List String
allReasons source =
    Pipeline.translateAll { project = "elm", name = "T", defName = "g" } source (Directives.read source)
        |> List.map (\f -> Pipeline.stageName f.stage ++ ":" ++ f.reason)


firstIsReported : String -> Expectation
firstIsReported source =
    case ( run source, List.head (Pipeline.translateAll { project = "elm", name = "T", defName = "g" } source (Directives.read source)) ) of
        ( Refused r, Just f ) ->
            if f.reason == r.reason || (r.reason == "type" && String.startsWith "unknown-type:" f.reason) then
                Expect.pass

            else
                Expect.fail (f.reason ++ " /= " ++ r.reason)

        ( Translated _, Nothing ) ->
            Expect.pass

        ( Translated _, Just f ) ->
            Expect.fail ("translated, but the report has " ++ f.reason)

        ( Refused r, Nothing ) ->
            Expect.fail ("refused with " ++ r.reason ++ ", but the report is empty")


{-| A worker test: its port declarations, its flags type, the FLAGS line (if any), init's body and
the logged message.
-}
worker : { ports : String, flagsType : String, flags : Maybe String, init : String, subs : String } -> String
worker w =
    "port module T exposing (main)\n-- TAGS: elm-spec\n"
        ++ (w.flags |> Maybe.map (\f -> "-- FLAGS: " ++ f ++ "\n") |> Maybe.withDefault "")
        ++ "-- CHECK: got: 1\n\nimport Platform\n\n"
        ++ w.ports
        ++ "\n\nmain : Program "
        ++ w.flagsType
        ++ " () Int\nmain =\n    Platform.worker\n        { init = \\flags -> ( (), "
        ++ w.init
        ++ " )\n        , update = \\msg model -> ( Debug.log \"got\" msg |> always model, Cmd.none )\n        , subscriptions = \\_ -> "
        ++ w.subs
        ++ "\n        }\n"


workerOutcome : { ports : String, flagsType : String, flags : Maybe String, init : String, subs : String } -> List String -> Expectation
workerOutcome w fragments =
    case run (worker w) of
        Translated t ->
            Expect.all
                ((\_ -> Expect.equal "worker" t.kind)
                    :: List.map (\f -> \_ -> (if String.contains f t.lean then Expect.pass else Expect.fail ("expected `" ++ f ++ "` in:\n" ++ t.lean))) fragments
                )
                ()

        Refused r ->
            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)


echoPorts : String
echoPorts =
    "port echoOut : Int -> Cmd msg\n\nport echoIn : (Int -> msg) -> Sub msg"


suite : Test
suite =
    describe "The translator"
        [ describe "all refusals (step 0 of plans/lean-full-definition.md)"
            [ test "a FLAGS directive is no refusal (step 5); Convert's refusals are reported" <|
                \_ ->
                    allReasons (program { imports = "import Dict\n", directives = "-- FLAGS: 1\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
                        |> List.take 1
                        |> Expect.equal [ "convert:import:Dict" ]
            , test "a compile-error test reports only its directive" <|
                \_ ->
                    allReasons (program { imports = "", directives = "-- COMPILE-ERROR: TYPE MISMATCH\n", decls = "", checks = [ ( "x", "1 + \"a\"", "1" ) ] })
                        |> Expect.equal [ "directives:compile-error" ]
            , test "a translated test reports no refusal" <|
                \_ -> allReasons (simple "" [ ( "x", "1 + 2", "3" ) ]) |> Expect.equal []
            , describe "the first refusal is the one translate reports"
                (List.indexedMap
                    (\i source -> test ("example " ++ String.fromInt i) <| \_ -> firstIsReported source)
                    [ program { imports = "", directives = "-- COMPILE-ERROR: TYPE MISMATCH\n", decls = "", checks = [ ( "x", "1", "1" ) ] }
                    , program { imports = "", directives = "-- FLAGS: 1\n", decls = "", checks = [ ( "x", "1", "1" ) ] }
                    , program { imports = "import Dict\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] }
                    , program { imports = "import Task\n", directives = "", decls = "t = Task.succeed 1", checks = [ ( "x", "1", "1" ) ] }
                    , simple "" [ ( "x", "String.fromInt 1", "\"1\"" ) ]
                    , simple "type alias P = { x : Int }" [ ( "x", "(P 1).x", "1" ) ]
                    , simple "" [ ( "x", "let { a } = { a = 1 } in a // 2", "0" ) ]
                    , simple "" [ ( "x", "1 + \"a\"", "1" ) ]
                    , simple ("big = 0\n" ++ String.repeat 2000 "-- padding padding\n") [ ( "x", "big", "0" ) ]
                    , simple "" [ ( "x", "1 + 2", "3" ) ]
                    ]
                )
            ]
        , describe "refusals"
            [ test "a compile-error test" <|
                \_ -> refusedWith "compile-error" (program { imports = "", directives = "-- COMPILE-ERROR: TYPE MISMATCH\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a FLAGS directive of a view program is no refusal" <|
                \_ -> translatedContaining [ "chk .check \"x: 1\"" ] (program { imports = "", directives = "-- FLAGS: 1\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "CHECK-DAG is read as CHECK; CHECK-NEXT follows its CHECK" <|
                \_ ->
                    translatedContaining [ "chk .check \"x: 1\"", "chk .next \"y: 2\"", "chk .check \"z: 3\"" ]
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\n-- CHECK-NEXT: y: 2\n-- CHECK-DAG: z: 3\nimport Html exposing (text)\nmain =\n    let\n        _ = Debug.log \"x\" 1\n        _ = Debug.log \"y\" 2\n        _ = Debug.log \"z\" 3\n    in\n    text \"done\"\n")
            , test "an unlabelled CHECK is kept as a label check" <|
                \_ -> translatedContaining [ "chk .check \"x\" " ] (program { imports = "", directives = "-- CHECK: x\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a regular-expression check is carried as printed" <|
                \_ -> translatedContaining [ "chk .check \"{{x: [0-9]+}}\" " ] (program { imports = "", directives = "-- CHECK: {{x: [0-9]+}}\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "an import outside the fragment" <|
                \_ -> refusedWith "import:Dict" (program { imports = "import Dict\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a restated default import is accepted" <|
                \_ -> translatedContaining [ "chk .check \"x: 1\" .float", "[str \"x\", .atexp (.paren (.atexp (.scon (.intF 1))))]" ] (program { imports = "import Basics exposing (..)\nimport Maybe exposing (Maybe(..))\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a value of Task is a value of the basis (step 5)" <|
                \_ -> translatedContaining [ "qv \"Task\" \"succeed\"" ] (program { imports = "import Task\n", directives = "", decls = "t = Task.succeed 1", checks = [ ( "x", "1", "1" ) ] })
            , test "an import of an effect module outside the basis" <|
                \_ -> refusedWith "effects" (program { imports = "import Time\n", directives = "", decls = "t = Time.now", checks = [ ( "x", "1", "1" ) ] })
            , test "a value of the basis the encoding does not include" <|
                \_ -> refusedWith "basis:String.fromInt" (simple "" [ ( "x", "String.fromInt 1", "\"1\"" ) ])
            , test "a library function outside the book's basis" <|
                \_ -> refusedWith "basis:Tuple.first" (simple "" [ ( "x", "Tuple.first ( 1, 2 )", "1" ) ])
            , test "a record alias constructor takes its fields in the order written" <|
                \_ -> translatedContaining [ "aliases := [(\"P\", some [\"y\", \"x\"])]", "ap (c \"P\") [i 1, i 2]" ] (simple "type alias P = { y : Int, x : Int }" [ ( "x", "(P 1 2).x", "2" ) ])
            , test "a value logged without a CHECK line is accepted" <|
                \_ ->
                    translatedContaining [ "chk .check \"x: 1\"" ]
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html exposing (text)\nmain =\n    let\n        _ = Debug.log \"x\" 1\n        _ = Debug.log \"y\" 2\n    in\n    text \"done\"\n")
            , test "a check whose label no Debug.log writes is refused (checks:unmatched)" <|
                \_ -> refusedWith "checks:unmatched:z" (program { imports = "", directives = "-- CHECK: z: 1\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a main that is not a let is a view (Html.text has the harness's scheme)" <|
                \_ -> translatedContaining [ ".fn \"main\" [] (ap (v \"text\") [str \"done\"])" ] "module T exposing (main)\n-- TAGS: elm-spec\nimport Html exposing (text)\nmain = text \"done\"\n"
            , test "a main that is not a view (construct:main-type)" <|
                \_ -> refusedWith "construct:main-type" "module T exposing (main)\n-- TAGS: elm-spec\nimport Html exposing (text)\nmain = 1\n"
            , test "a main with arguments (construct:main-shape)" <|
                \_ -> refusedWith "construct:main-shape" "module T exposing (main)\n-- TAGS: elm-spec\nimport Html exposing (text)\nmain x = text \"done\"\n"
            , test "a main annotated Html msg is a view" <|
                \_ -> translatedContaining [ ".fn \"main\"" ] "module T exposing (main)\n-- TAGS: elm-spec\nimport Html exposing (Html, text)\nmain : Html msg\nmain = text \"done\"\n"
            , test "EXIT 1 with CHECK-NOT gives a program expected to have no meaning" <|
                \_ -> translatedContaining [ "chk .not_ \"y:\"", "meaning := false" ] (program { imports = "", directives = "-- EXIT: 1\n-- CHECK-NOT: y:\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a check logged inside a function is accepted" <|
                \_ -> translatedContaining [ "chk .check \"f: 2\" .int" ] (program { imports = "", directives = "-- CHECK: f: 2\n", decls = "f : Int -> Int\nf n =\n    Debug.log \"f\" (n * 2)", checks = [ ( "x", "f 1", "2" ) ] })
            , test "the shape of a check is the logged value's inferred type" <|
                \_ -> translatedContaining [ "chk .check \"x: 3\" .int", "chk .check \"s: \\\"a\\\"\" .string" ] (simple "" [ ( "x", "7 // 2", "3" ), ( "s", "\"a\"", "\"a\"" ) ])
            , test "a CHECK-NOT line without EXIT 1" <|
                \_ -> refusedWith "checks:check-not" (program { imports = "", directives = "-- CHECK-NOT: y:\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "an exit status other than 0, or 1 with a CHECK-NOT" <|
                \_ -> refusedWith "checks:exit" (program { imports = "", directives = "-- EXIT: 2\n", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "a check logged by a pipe" <|
                \_ ->
                    translatedContaining [ "chk .check \"x: 1\"" ]
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html exposing (text)\nmain =\n    let\n        _ = 1 |> Debug.log \"x\"\n    in\n    text \"done\"\n")
            , test "a record pattern binding needed at Int (its variables are the fields, so they cannot be renamed for a copy)" <|
                \_ -> refusedWith "number" (simple "" [ ( "x", "let { a } = { a = 1 } in a // 2", "0" ) ])
            , test "a program that does not type" <|
                \_ -> refusedWith "type" (simple "" [ ( "x", "1 + \"a\"", "1" ) ])
            , test "a program too large" <|
                \_ -> refusedWith "construct:large-program" (simple ("big = 0\n" ++ String.repeat 2000 "-- padding padding\n") [ ( "x", "big", "0" ) ])
            ]
        , describe "modules"
            [ test "a helper module is read from the project's src folder and comes before the test" <|
                \_ ->
                    withHelpers [ ( "H", "module H exposing (double)\n\ndouble : Int -> Int\ndouble n = n * 2\n" ) ]
                        [ "helpers := [", "{ name := \"H\", path := \"tests/elm/src/H.elm\"", "ap (v \"double\") [i 2]", "⟨\"H\", \"H\", some (.items [.var \"double\"])⟩" ]
                        (mainWith "import H exposing (double)" "x: 4" "double 2")
            , test "modules are ordered after the modules they import (post-order, imports in written order)" <|
                \_ ->
                    case runWith [ ( "A", "module A exposing (a)\n\nimport B\n\na : Int\na = B.b + 1\n" ), ( "B", "module B exposing (b)\n\nb : Int\nb = 1\n" ) ] (mainWith "import A" "x: 2" "A.a") of
                        Translated t ->
                            case ( String.indexes "name := \"B\"" t.lean, String.indexes "name := \"A\"" t.lean ) of
                                ( b :: _, a :: _ ) ->
                                    Expect.lessThan a b

                                _ ->
                                    Expect.fail t.lean

                        Refused r ->
                            Expect.fail r.reason
            , test "an import cycle is refused (import:cycle)" <|
                \_ ->
                    refusedWithHelpers [ ( "A", "module A exposing (a)\n\nimport B\n\na = 1\n" ), ( "B", "module B exposing (b)\n\nimport A\n\nb = 2\n" ) ]
                        "import:cycle"
                        (mainWith "import A" "x: 1" "A.a")
            , test "a value of the basis an import's exposing list brings in is kept as written (unqualified)" <|
                \_ ->
                    case run (mainWith "import Char exposing (toCode)" "x: 97" "toCode 'a' + Char.toCode 'b' - 98") of
                        Translated t ->
                            Expect.all
                                [ \lean -> Expect.equal True (String.contains "ap (v \"toCode\") [.atexp (chA 'a')]" lean)
                                , \lean -> Expect.equal True (String.contains "ap (qv \"Char\" \"toCode\") [.atexp (chA 'b')]" lean)
                                , \lean -> Expect.equal True (String.contains "(ap (v \"text\") [str \"done\"])" lean)
                                , \lean -> Expect.equal False (String.contains "qv \"Html\" \"text\"" lean)
                                ]
                                t.lean

                        Refused r ->
                            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)
            , test "a qualified value of a helper is written qualified" <|
                \_ ->
                    withHelpers [ ( "H", "module H exposing (..)\n\nk : Int\nk = 3\n" ) ] [ "qv \"Q\" \"k\"", "⟨\"H\", \"Q\", none⟩" ] (mainWith "import H as Q" "x: 3" "Q.k")
            , test "two helpers' types of one name are distinct types (qualified type names)" <|
                \_ ->
                    refusedWithHelpers [ ( "H1", "module H1 exposing (T(..))\n\ntype T = A Int\n" ), ( "H2", "module H2 exposing (T(..))\n\ntype T = B Int\n" ) ]
                        "type"
                        (mainWith "import H1\nimport H2\n\nf : H1.T -> Int\nf t =\n    case t of\n        H1.A n -> n\n" "x: 1" "f (H2.B 1)")
            , test "a later import's type replaces an earlier one's (ImportTypeByNameLaterReplacesTest)" <|
                \_ ->
                    withHelpers [ ( "H1", "module H1 exposing (T(..))\n\ntype T = A Int\n" ), ( "H2", "module H2 exposing (T(..), mk)\n\ntype T = B Int\n\nmk : Int -> T\nmk n = B n\n" ) ]
                        [ "ap (v \"mk\") [i 7]" ]
                        (mainWith "import H1 exposing (T)\nimport H2 exposing (T, mk)\n\ng : T -> T\ng t = t\n" "x: B 7" "g (mk 7)")
            , test "an exposing item of a declaration copied at Int stands for the copy, in the header and in the importer's list" <|
                \_ ->
                    withHelpers [ ( "H", "module H exposing (inc)\n\ninc n = n + 1\n" ) ]
                        [ "exposing := (.items [.var \"inc\", .var \"inc$Int\"])", "some (.items [.var \"inc\", .var \"inc$Int\"])", "ap (v \"inc$Int\")" ]
                        (mainWith "import H exposing (inc)" "x: 4" "inc (7 // 2)")
            , test "a constructor of a helper's type exposed with (..)" <|
                \_ ->
                    withHelpers [ ( "H", "module H exposing (Shape(..))\n\ntype Shape = Circle Int | Square Int\n" ) ]
                        [ "types := [(\"Shape\", [(\"Circle\", 1), (\"Square\", 1)])]", "ap (c \"Circle\") [i 2]" ]
                        (mainWith "import H exposing (Shape(..))" "x: Circle 2" "Circle 2")
            , test "a check logged in a helper module is accepted" <|
                \_ ->
                    withHelpers [ ( "H", "module H exposing (f)\n\nf : Int -> Int\nf n = Debug.log \"h\" (n + 1)\n" ) ]
                        [ "chk .check \"h: 2\" .int" ]
                        ("module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: h: 2\nimport Html exposing (text)\nimport H\nmain =\n    let\n        _ = H.f 1\n    in\n    text \"done\"\n")
            , test "an outgoing port of Bool has direction out and payload .bool" <|
                \_ ->
                    translatedContaining [ "ports := [(\"out\", .out, .bool)]" ]
                        "port module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html\n\nport out : Bool -> Cmd msg\n\nmain =\n    let\n        _ = Debug.log \"x\" 1\n    in\n    Html.text \"done\"\n"
            , test "an incoming port of a 3-tuple has direction in and payload .tuple3" <|
                \_ ->
                    translatedContaining [ "ports := [(\"inp\", .inn, (.tuple3 .int .string .bool))]" ]
                        "port module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html\nimport Platform.Sub exposing (Sub)\n\nport inp : (( Int, String, Bool ) -> msg) -> Sub msg\n\nmain =\n    let\n        _ = Debug.log \"x\" 1\n    in\n    Html.text \"done\"\n"
            , test "a record payload's fields are sorted by label" <|
                \_ ->
                    translatedContaining [ "(.maybe (.record (.cons \"a\" .int (.cons \"b\" .string .nil))))" ]
                        "port module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html\n\nport out : Maybe { b : String, a : Int } -> Cmd msg\n\nmain =\n    let\n        _ = Debug.log \"x\" 1\n    in\n    Html.text \"done\"\n"
            , test "a port of a function type is refused (construct:port-type)" <|
                \_ ->
                    refusedWith "construct:port-type"
                        "port module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 1\nimport Html\n\nport out : (Int -> Int) -> Cmd msg\n\nmain =\n    let\n        _ = Debug.log \"x\" 1\n    in\n    Html.text \"done\"\n"
            , test "main of type Program is a worker test (step 5)" <|
                \_ ->
                    case run "module T exposing (main)\n-- TAGS: elm-spec\n\nmain : Program () () ()\nmain =\n    Debug.todo \"worker\"\n" of
                        Translated t ->
                            Expect.equal "worker" t.kind

                        Refused r ->
                            Expect.fail r.reason
            , test "an import of a basis module without its values is accepted" <|
                \_ -> translatedContaining [ "⟨\"Array\", \"Array\", none⟩" ] (program { imports = "import Array\n", directives = "", decls = "", checks = [ ( "x", "1", "1" ) ] })
            , test "the manifest lists every module of the program" <|
                \_ ->
                    case runWith [ ( "H", "module H exposing (k)\n\nk : Int\nk = 3\n" ) ] (mainWith "import H" "x: 3" "H.k") of
                        Translated t ->
                            Expect.equal [ "tests/elm/src/H.elm", "tests/elm/src/T.elm" ] t.sources

                        Refused r ->
                            Expect.fail r.reason
            ]
        , describe "inference of literal types"
            [ test "a literal under / is Float" <|
                \_ -> translatedContaining [ "bin \"/\" (.atexp (.scon (.intF 1))) (.atexp (.scon (.intF 2)))" ] (simple "" [ ( "x", "1 / 2", "0.5" ) ])
            , test "a literal under // is Int" <|
                \_ -> translatedContaining [ "bin \"//\" (i 7) (i 2)" ] (simple "" [ ( "x", "7 // 2", "3" ) ])
            , test "a literal alone is Float by default (ruling A27)" <|
                \_ -> translatedContaining [ "chk .check \"x: 3\" .float", "bin \"+\" (.atexp (.scon (.intF 1))) (.atexp (.scon (.intF 2)))" ] (simple "" [ ( "x", "1 + 2", "3" ) ])
            , test "through a record field" <|
                \_ -> translatedContaining [ "recE [(\"a\", .atexp (.scon (.intF 1)))]" ] (simple "r = { a = 1 }" [ ( "x", "r.a / 2", "0.5" ) ])
            , test "through Maybe and a case" <|
                \_ -> translatedContaining [ ".atexp (.scon (.intF 2))" ] (simple "m = Just 2" [ ( "x", "case m of\n                Just y -> y / 4\n                Nothing -> 0", "0.5" ) ])
            , test "through a lambda" <|
                \_ -> translatedContaining [ "lams [pv \"z\"] (bin \"+\" (v \"z\") (.atexp (.scon (.intF 1))))" ] (simple "" [ ( "x", "(\\z -> z + 1) 0.5", "1.5" ) ])
            , test "a hex literal is exact" <|
                \_ -> translatedContaining [ "i 18446744073709551615" ] (simple "" [ ( "x", "0xFFFFFFFFFFFFFFFF // 1", "-1" ) ])
            , test "a literal after an astral character on its line" <|
                \_ -> translatedContaining [ "chk .check \"x: ( '😀', 12 )\" .data", "tup2 (.atexp (chA '😀')) (.atexp (.scon (.intF 12)))" ] (simple "" [ ( "x", "( '😀', 12 )", "( '😀', 12 )" ) ])
            , test "a negative literal is a negation" <|
                \_ -> translatedContaining [ ".atexp (neg (A (i 7)))" ] (simple "" [ ( "x", "-7 // 1", "-7" ) ])
            ]
        , describe "number specialisation"
            [ test "a declaration used at Int and Float gets two copies" <|
                \_ ->
                    translatedContaining [ ".fn \"inc\" [pv \"n\"] (bin \"+\" (v \"n\") (.atexp (.scon (.intF 1))))", ".fn \"inc$Int\" [pv \"n\"] (bin \"+\" (v \"n\") (i 1))", "ap (v \"inc\") [.atexp (.scon (.float", "ap (v \"inc$Int\")" ]
                        (simple "inc n = n + 1" [ ( "x", "inc 0.5", "1.5" ), ( "y", "inc (7 // 2)", "4" ) ])
            , test "an unused declaration keeps its default copy" <|
                \_ -> translatedContaining [ ".fn \"unused\" [pv \"n\"] (bin \"*\" (v \"n\") (.atexp (.scon (.intF 2))))" ] (simple "unused n = n * 2" [ ( "x", "1", "1" ) ])
            , test "an annotated number function" <|
                \_ ->
                    translatedContaining [ ".fn \"twice$Int\"" ]
                        (simple "twice : number -> number\ntwice n = n * 2" [ ( "x", "twice (7 // 2)", "6" ) ])
            , test "an annotated number function used at Int computes at Int, at Float at Float" <|
                \_ ->
                    translatedContaining
                        [ ".fn \"myfun\" [pv \"x\"] (bin \"^\" (v \"x\") (.atexp (neg (.scon (.intF 1)))))"
                        , ".fn \"myfun$Int\" [pv \"x\"] (bin \"^\" (v \"x\") (.atexp (neg (A (i 1)))))"
                        , "ap (v \"myfun$Int\")"
                        ]
                        (simple "myfun : number -> number\nmyfun x =\n    x ^ -1" [ ( "x", "myfun (2 // 1)", "0" ), ( "y", "myfun 2", "0.5" ) ])
            , test "a pattern binding used at Float is copied, every variable renamed (one word per number variable: a, then b)" <|
                \_ -> translatedContaining [ ".pat (ptup2 (P (pv \"a$Float$Int\")) (P (pv \"b$Float$Int\")))", "v \"a$Float$Int\"" ] (simple "" [ ( "x", "let ( a, b ) = ( 1, 2 ) in a / 2 + toFloat (b // 1)", "2.5" ) ])
            , test "isNaN and isInfinite are values of E0" <|
                \_ -> translatedContaining [ "ap (v \"isNaN\")", "ap (v \"isInfinite\")" ] (simple "" [ ( "x", "isNaN (0 / 0)", "True" ), ( "y", "isInfinite (1 / 0)", "True" ) ])
            , test "++ is the operator of append, at String and at List" <|
                \_ -> translatedContaining [ "bin \"++\" (str \"a\") (str \"b\")", "bin \"++\" (listE [.atexp (.scon (.intF 1))]) (listE [.atexp (.scon (.intF 2))])" ] (simple "" [ ( "x", "\"a\" ++ \"b\"", "\"ab\"" ), ( "y", "[ 1 ] ++ [ 2 ]", "[1,2]" ) ])
            , test "the conversions: a program that uses round is checked natively" <|
                \_ -> translatedContaining [ "native := true", "ap (v \"round\")", "ap (v \"toFloat\") [i 2]" ] (simple "" [ ( "x", "round 1.5", "2" ), ( "y", "toFloat 2", "2" ) ])
            , test "toFloat and sqrt alone are computed by the kernel" <|
                \_ -> translatedContaining [ "def g : Program := {\n  name := \"T\", source := \"tests/elm/src\",\n" ] (simple "" [ ( "x", "sqrt (toFloat 4)", "2" ) ])
            , test "^ at Float is ^, its program checked natively" <|
                \_ -> translatedContaining [ "native := true", "bin \"^\" (.atexp (.scon (.float 20 (-1))))" ] (simple "" [ ( "x", "2.0 ^ 2", "4" ) ])
            , test "^ at Int stays with the kernel" <|
                \_ -> translatedContaining [ "def g : Program := {\n  name := \"T\", source := \"tests/elm/src\",\n", "bin \"^\" (i 2) (i 3)" ] (simple "" [ ( "x", "2 ^ 3 // 1", "8" ) ])
            , test "Char.toCode, Char.fromCode and Debug.toString are qualified values of E0" <|
                \_ -> translatedContaining [ "qv \"Char\" \"toCode\"", "qv \"Char\" \"fromCode\"", "qv \"Debug\" \"toString\"", "native := true" ] (simple "" [ ( "x", "Char.toCode 'a'", "97" ), ( "y", "Char.fromCode 98", "'b'" ), ( "z", "Debug.toString 1", "\"1\"" ) ])
            , test "abs at Int is its copy at Int" <|
                \_ -> translatedContaining [ "v \"abs$Int\"" ] (simple "" [ ( "x", "abs (3 // -1)", "3" ) ])
            , test "a group's number variables are in first-occurrence order over its members' types, members in group order (step 10, Choices, item 2)" <|
                \_ ->
                    -- f's type reads abe's variable first (record fields in label order), g's
                    -- zed's; the group's order is f's, so the copy at zed Int, abe Float is $Float$Int
                    translatedContaining [ ".fn \"f$Float$Int\"", ".fn \"g$Float$Int\"", "ap (v \"f$Float$Int\")" ]
                        (simple "f { zed, abe } stop =\n    if stop then ( zed + 1, abe + 1 ) else g zed abe True\n\ng zed abe stop =\n    f { zed = zed, abe = abe } stop"
                            [ ( "x", "case f { zed = 1 // 1, abe = 0.5 } False of\n                ( a, b ) -> toFloat a + b", "3.5" ) ]
                        )
            , test "an occurrence inside its own group takes the enclosing copy's number for a variable its scheme does not bind (step 10, Choices, item 5)" <|
                \_ ->
                    -- the group's variables are g's (Int at `g (3 // 1)`), then f's (Float); in the
                    -- copy at (Int, Float), f's scheme binds only its own variable, g's is the
                    -- copy's Int, so `f 1` refers to the same copy (Float before the change)
                    translatedContaining [ ".fn \"g$Int$Float\" [pv \"y\"] (letDefs [.pat pw (ap (v \"f$Int$Float\")", "(ap (v \"f$Int$Float\") [.atexp (.paren" ]
                        (simple "g y =\n    let\n        _ = f 1\n    in\n    y + 1\n\nf : number -> number\nf x =\n    if x > 3 then x else let _ = g 2 in f (x + 1)"
                            [ ( "x", "g (3 // 1)", "4" ) ]
                        )
            , test "outside its group, a variable of the group that the occurrence's scheme does not bind is Float, not the enclosing copy's (finding of 2026-11-12)" <|
                \_ ->
                    -- g's scheme (Bool) does not bind the group's number variable (f's U'); inside
                    -- h$Int the occurrence of g refers to g, and no copy of f or g at Int is made
                    translatedLackingAnd [ "g$Int", "f$Int" ] [ ".fn \"h$Int\"" ]
                        (simple "f : number -> number\nf x =\n    if g then x else x\n\ng =\n    f 1 == f 2\n\nh : number -> number\nh y =\n    y + (if g then 1 else 1)"
                            [ ( "x", "h 1 // 2", "1" ) ]
                        )
            , test "ruling A93: a group's number variable a use does not fix is Float" <|
                \_ ->
                    translatedContaining [ "bin \"^\" (ap (v \"g\") [.atexp (.scon (.intF 1))" ]
                        (simple "f n =\n    if n <= 0 then 0 else if g 1 (n - 1) ^ -1 > 0 then 1 else 0\n\ng y k =\n    if k <= 0 then y + 1 else let _ = f k in y + 1" [ ( "f 3", "f 3", "1" ) ])
            ]
        , describe "worker tests (plan step 5)"
            [ test "a JSON number is exact: digits and a power of ten" <|
                \_ -> Json.parse "-12.50e1" |> Expect.equal (Just (Json.JNum "-1250" -1))
            , test "the numerals of the specification, exactly" <|
                \_ ->
                    List.map Json.parse [ "42", "1e300", "-1.5e3", "0.1", "123456789012345678901" ]
                        |> Expect.equal
                            [ Just (Json.JNum "42" 0)
                            , Just (Json.JNum "1" 300)
                            , Just (Json.JNum "-15" 2)
                            , Just (Json.JNum "1" -1)
                            , Just (Json.JNum "123456789012345678901" 0)
                            ]
            , test "-0 is the number 0 (A88)" <|
                \_ -> Json.parse "-0" |> Expect.equal (Just (Json.JNum "0" 0))
            , test "a large integer keeps its digits" <|
                \_ -> Json.parse "9007199254740993" |> Expect.equal (Just (Json.JNum "9007199254740993" 0))
            , test "objects, arrays, strings with escapes" <|
                \_ ->
                    Json.parse " {\"a\" : [1, true, null], \"b\": \"x\\ny\"} "
                        |> Expect.equal (Just (Json.JObj [ ( "a", Json.JArr [ Json.JNum "1" 0, Json.JTrue, Json.JNull ] ), ( "b", Json.JStr "x\ny" ) ]))
            , test "a trailing comma is not JSON" <|
                \_ -> Json.parse "[1,]" |> Expect.equal Nothing
            , test "an object is written through mkObj" <|
                \_ -> Maybe.map Json.toLean (Json.parse "{\"k\":1}") |> Expect.equal (Just "(Eff.BVal.mkObj [(\"k\", (.num (Eff.jnum (1) (0))))])")
            , test "a worker is translated with its worker test, flags absent are null (A72)" <|
                \_ ->
                    workerOutcome { ports = "", flagsType = "()", flags = Nothing, init = "Cmd.none", subs = "Sub.none" }
                        [ "def w : Prog.WorkerTest := {", "flagsType := .unit", "flags := .null", "host := .none" ]
            , test "the flags are the FLAGS line's JSON at the flags type" <|
                \_ ->
                    workerOutcome { ports = "", flagsType = "{ n : Int }", flags = Just "{\"n\": 1}", init = "Cmd.none", subs = "Sub.none" }
                        [ "flags := (Eff.BVal.mkObj [(\"n\", (.num (Eff.jnum (1) (0))))])" ]
            , test "a record flags type has its fields sorted by label (FlagsRecordTest)" <|
                \_ ->
                    workerOutcome { ports = "", flagsType = "{ label : String, count : Int, enabled : Bool }", flags = Just "{\"count\":42,\"label\":\"x\",\"enabled\":true}", init = "Cmd.none", subs = "Sub.none" }
                        [ "flagsType := (.record (.cons \"count\" .int (.cons \"enabled\" .bool (.cons \"label\" .string .nil))))" ]
            , test "an outgoing port alone installs no host (OutgoingPortTuple3Test)" <|
                \_ ->
                    workerOutcome { ports = "port out3 : Int -> Cmd msg", flagsType = "()", flags = Nothing, init = "out3 1", subs = "Sub.none" }
                        [ "host := .none" ]
            , test "the A81 test's CHECK-NOT is dropped, with its reason (finding T1)" <|
                \_ ->
                    Directives.read "-- CHECK: a: 1\n-- CHECK-NOT: the long sleep ended\n"
                        |> Directives.dropCheckNots "StandardA81SleepBeyond32BitsTest"
                        |> (\d -> ( List.length d.lines, d.dropped, d.refusal ))
                        |> Expect.equal ( 1, [ "CHECK-NOT: the long sleep ended (finding T1: r:p-wait lets the long sleep end before the kill; not required by the book, theorem t1_a81_long_sleep_may_end)" ], Nothing )
            , test "a CHECK-NOT proved by hand is carried as a pattern, not refused (plan step 6)" <|
                \_ ->
                    Directives.read "-- CHECK: result: 1\n-- CHECK-NOT: handler called\n"
                        |> Directives.dropCheckNots "TaskOnErrorSucceedTest"
                        |> (\d -> ( List.length d.lines, d.checkNots, d.refusal ))
                        |> Expect.equal ( 1, [ "handler called" ], Nothing )
            , test "any other CHECK-NOT stays refused" <|
                \_ ->
                    Directives.read "-- CHECK: result: 1\n-- CHECK-NOT: handler called\n"
                        |> Directives.dropCheckNots "SomeOtherTest"
                        |> .refusal
                        |> Expect.equal (Just "checks:check-not")
            , test "worker choices: leaf order, fuel and overrides, written before the checks" <|
                \_ ->
                    Decode.decodeString Choices.decoder "{\"elm/T\": {\"leafOrder\": \"listed\", \"fuel\": 9, \"overrides\": [{\"at\": 2, \"choice\": {\"wait\": \"1.5\"}}, {\"at\": 3, \"choice\": \"update\"}]}}"
                        |> Result.toMaybe
                        |> Maybe.andThen (Dict.get "elm/T")
                        |> Maybe.map (\f -> Choices.apply f "def w : Prog.WorkerTest := {\n  host := .none,\n  checks := [] }")
                        |> Expect.equal (Just "def w : Prog.WorkerTest := {\n  host := .none,\n  sched := { leafOrder := .listed, overrides := [(2, (.wait (Eff.jnum (15) (-1)))), (3, .update)] },\n  fuel := 9,\n  checks := [] }")
            , test "FLAGS that are not JSON are refused" <|
                \_ -> refusedWith "construct:flags" (worker { ports = "", flagsType = "Int", flags = Just "{oops", init = "Cmd.none", subs = "Sub.none" })
            , test "echoOut and echoIn, both used, install the echo host" <|
                \_ ->
                    workerOutcome { ports = echoPorts, flagsType = "()", flags = Nothing, init = "echoOut 1", subs = "echoIn identity" }
                        [ "host := .echo \"echoOut\" \"echoIn\"" ]
            , test "an unused echoIn installs no host (Elm/JS leaves it out of app.ports)" <|
                \_ ->
                    workerOutcome { ports = echoPorts, flagsType = "()", flags = Nothing, init = "echoOut 1", subs = "Sub.none" }
                        [ "host := .none" ]
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
