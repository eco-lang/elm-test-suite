module SourceTest exposing (suite)

{-| The source-syntax writer (plans/lean-full-definition/step-08-source-syntax.md, "Unit tests"),
behind eco's parser and the front end (plans/eco-parser.md, E7).
-}

import Expect exposing (Expectation)
import Test exposing (Test, describe, test)
import Translate.FrontEnd as FrontEnd
import Translate.Parse as Parse
import Translate.Source as Source


write : List ( String, String ) -> Result String String
write modules =
    modules
        |> List.map
            (\( name, text ) ->
                let
                    path =
                        "tests/elm/src/" ++ name ++ ".elm"
                in
                case Parse.parse text of
                    Ok file ->
                        case FrontEnd.check { path = path, source = text } file of
                            r :: _ ->
                                Err r.reason

                            [] ->
                                Ok { path = path, source = text, file = file }

                    Err _ ->
                        Err ("parse: " ++ name)
            )
        |> List.foldr (Result.map2 (::)) (Ok [])
        |> Result.andThen
            (\ms ->
                Source.program { project = "elm", name = "T", defName = "s_elm_T" } ms
                    |> Result.mapError .reason
            )


one : String -> Result String String
one body =
    write [ ( "T", "module T exposing (main)\n\nimport Html\n\n" ++ body ++ "\n" ) ]


contains : List String -> Result String String -> Expectation
contains fragments r =
    case r of
        Ok lean ->
            Expect.all
                (List.map
                    (\f ->
                        \l ->
                            if String.contains f l then
                                Expect.pass

                            else
                                Expect.fail ("expected `" ++ f ++ "` in:\n" ++ l)
                    )
                    fragments
                )
                lean

        Err e ->
            Expect.fail ("refused: " ++ e)


suite : Test
suite =
    describe "The source syntax"
        [ test "0x10 and 16 are the integer 16; a large integer is written exactly" <|
            \_ -> one "a = 0x10\n\nb = 16\n\nc = 9007199254740993\n\nmain = Html.text \"\"" |> contains [ "Src.val \"a\" none [] (Src.i 16)", "Src.val \"b\" none [] (Src.i 16)", "Src.i 9007199254740993" ]
        , test "a unicode escape is its character; the front end refuses a lone surrogate" <|
            \_ ->
                Expect.all
                    [ \_ -> one "a = '\\u{0041}'\n\nmain = Html.text \"\"" |> contains [ "Src.ch 'A'" ]
                    , \_ -> one "a = '\\u{1F600}'\n\nb = \"x\\u{1F600}\"\n\nmain = Html.text \"\"" |> contains [ "Src.ch '😀'", "Src.str \"x😀\"" ]
                    , \_ -> one "a = '\\u{D800}'\n\nmain = Html.text \"\"" |> Expect.equal (Err "syntax:core-escape-unicode")
                    ]
                    ()
        , test "an else-if chain is one ifte; with parentheses, two" <|
            \_ ->
                Expect.all
                    [ \_ -> one "f a b c d e = if a then b else if c then d else e\n\nmain = Html.text \"\"" |> contains [ ".ifte [(Src.v \"a\", Src.v \"b\"), (Src.v \"c\", Src.v \"d\")] (Src.v \"e\")" ]
                    , \_ -> one "f a b c d e = if a then b else (if c then d else e)\n\nmain = Html.text \"\"" |> contains [ ".ifte [(Src.v \"a\", Src.v \"b\")] (.paren (.ifte [(Src.v \"c\", Src.v \"d\")]" ]
                    ]
                    ()
        , test "operators are grouped by the book's fixities; && is a binop" <|
            \_ -> one "f a b c = a + b * c\n\ng a b = a && b\n\nh a b c = a :: b :: c\n\nmain = Html.text \"\"" |> contains [ "Src.bin \"+\" (Src.v \"a\") (Src.bin \"*\" (Src.v \"b\") (Src.v \"c\"))", "Src.bin \"&&\"", "Src.bin \"::\" (Src.v \"a\") (Src.bin \"::\" (Src.v \"b\") (Src.v \"c\"))" ]
        , test "a negative constant after [ is parsed (elm-syntax rejected it)" <|
            \_ -> one "a = [-3, -2]\n\nmain = Html.text \"\"" |> contains [ ".list [.neg (Src.i 3), .neg (Src.i 2)]" ]
        , test "the fields of a record pattern keep their source order" <|
            \_ -> one "f { b, a } = a\n\nmain = Html.text \"\"" |> contains [ ".record [\"b\", \"a\"]" ]
        , test "an annotation is kept with its definition" <|
            \_ -> one "f : Int -> Int\nf x = x\n\nmain = Html.text \"\"" |> contains [ "Src.val \"f\" (some (.fn (Src.tc \"Int\" []) (Src.tc \"Int\" []))) [Src.pv \"x\"] (Src.v \"x\")" ]
        , test "a record update and a field accessor" <|
            \_ -> one "f r = { r | x = 1 }\n\ng = .x\n\nmain = Html.text \"\"" |> contains [ ".update \"r\" [(\"x\", Src.i 1)]", ".accessor \"x\"" ]
        , test "a port module with one port" <|
            \_ ->
                write [ ( "T", "port module T exposing (main)\n\nimport Html\n\nport out : Int -> Cmd msg\n\nmain = Html.text \"\"\n" ) ]
                    |> contains [ "Src.hdr true \"T\"", ".port \"out\"" ]
        , test "a helper module comes before the test" <|
            \_ ->
                write [ ( "H", "module H exposing (k)\n\nk = 1\n" ), ( "T", "module T exposing (main)\n\nimport H\nimport Html\n\nmain = Html.text \"\"\n" ) ]
                    |> Result.map (\l -> ( String.indexes "Src.hdr false \"H\"" l, String.indexes "Src.hdr false \"T\"" l ))
                    |> Result.map (\( h, t ) -> List.head h |> Maybe.map2 (\tt hh -> hh < tt) (List.head t))
                    |> Expect.equal (Ok (Just True))
        , test "a tuple of four in a type is refused by the front end (so never written)" <|
            \_ -> one "f : ( Int, Int, Int, Int ) -> Int\nf x = 1\n\nmain = Html.text \"\"" |> Expect.equal (Err "syntax:tuple-arity")
        , test "a destructuring at top level is not parsed by eco's parser; in a let it is a pattern definition" <|
            \_ ->
                Expect.all
                    [ \_ -> one "( a, b ) = ( 1, 2 )\n\nmain = Html.text \"\"" |> Expect.equal (Err "parse: T")
                    , \_ -> one "f = let ( a, b ) = ( 1, 2 ) in a\n\nmain = Html.text \"\"" |> contains [ ".letE [.pat (.tuple [Src.pv \"a\", Src.pv \"b\"])" ]
                    ]
                    ()
        ]
