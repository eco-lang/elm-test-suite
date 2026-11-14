module ParseTest exposing (suite)

{-| The translator's entry to eco's parser (plans/eco-parser.md, E4, step 2).
-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Compiler.Parse.Declaration as Decl
import Expect
import Test exposing (Test, describe, test)
import Translate.Parse as Parse


names : Parse.Parsed -> List String
names p =
    List.map
        (\d ->
            case d of
                Decl.Value _ (A.At _ (Src.Value v)) ->
                    A.toValue (Parse.c1 v.name)

                Decl.Union _ (A.At _ (Src.Union ( _, A.At _ n ) _ _ _)) ->
                    n

                Decl.Alias _ (A.At _ (Src.Alias a)) ->
                    A.toValue (Parse.c2 a.name)

                Decl.Port _ (Src.Port _ ( _, A.At _ n ) _) ->
                    n
        )
        (Parse.declarations p)


suite : Test
suite =
    describe "Translate.Parse"
        [ test "a small module parses, with its name and exposing list" <|
            \_ ->
                Parse.parse "module M exposing (f, T(..))\n\nf = 1\n"
                    |> Result.map (\p -> ( Parse.moduleName p, Parse.isPortModule p, Parse.exposing_ p /= Src.Open [] [] ))
                    |> Expect.equal (Ok ( Just "M", False, True ))
        , test "a negative constant right after [ parses" <|
            \_ ->
                Parse.parse "module M exposing (x)\n\nx = [-3, -2]\n"
                    |> Result.map names
                    |> Expect.equal (Ok [ "x" ])
        , test "a bad hex digit does not parse, and the failure says where" <|
            \_ ->
                case Parse.parse "module M exposing (x)\n\nx = 0x1G\n" of
                    Err d ->
                        Expect.equal True (String.startsWith "3:8 " d)

                    Ok _ ->
                        Expect.fail "parsed"
        , test "imports and declarations are kept in source order" <|
            \_ ->
                Parse.parse "port module M exposing (..)\n\nimport B as Bee exposing (b)\nimport A\n\ntype T = T\n\nz = 1\n\nport p : Int -> Cmd msg\n\ntype alias R = {}\n\na = 2\n"
                    |> Result.map
                        (\p ->
                            ( List.map (\i -> ( i.name, i.alias, i.row )) (Parse.importsOf p)
                            , names p
                            , Parse.isPortModule p
                            )
                        )
                    |> Expect.equal (Ok ( [ ( "B", Just "Bee", 3 ), ( "A", Nothing, 4 ) ], [ "T", "z", "p", "R", "a" ], True ))
        , test "a file without a header has none" <|
            \_ ->
                Parse.parse "x = 1\n"
                    |> Result.map .header
                    |> Expect.equal (Ok Nothing)
        , test "an import without an exposing list has none" <|
            \_ ->
                Parse.parse "module M exposing (x)\n\nimport A\nimport B exposing (..)\n\nx = 1\n"
                    |> Result.map (Parse.importsOf >> List.map (.exposing_ >> (/=) Nothing))
                    |> Expect.equal (Ok [ False, True ])
        , test "string and character literals are decoded" <|
            \_ ->
                ( Parse.stringValue "a\\u0041\\n", Parse.charValue "\\uD83D\\uDE00" )
                    |> Expect.equal ( "aA\n", '😀' )
        , test "the fields of a record pattern are in source order" <|
            \_ ->
                case Parse.parse "module M exposing (f)\n\nf { b, a, c } = a\n" |> Result.map Parse.functions of
                    Ok [ f ] ->
                        case f.args of
                            [ A.At _ (Src.PRecord fields) ] ->
                                Parse.recordPatternFields fields |> List.map A.toValue |> Expect.equal [ "b", "a", "c" ]

                            _ ->
                                Expect.fail "not a record pattern"

                    _ ->
                        Expect.fail "did not parse"
        ]
