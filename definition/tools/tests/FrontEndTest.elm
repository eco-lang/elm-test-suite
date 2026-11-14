module FrontEndTest exposing (suite)

{-| The front end's checks (plans/eco-parser.md, E6, step 4): one per row of E6's table, positive
and negative.
-}

import Expect
import Test exposing (Test, describe, test)
import Translate.FrontEnd as FrontEnd
import Translate.Parse as Parse


{-| The front end's refusals of a module, as `reason@row:col`, or the parse failure.
-}
check : String -> Result String (List String)
check text =
    Parse.parse text
        |> Result.map
            (\p ->
                FrontEnd.check { path = "M.elm", source = text } p
                    |> List.map (\r -> r.reason ++ "@" ++ String.fromInt r.at.start.row ++ ":" ++ String.fromInt r.at.start.column)
            )


body : String -> Result String (List String)
body text =
    check ("module M exposing (..)\n\n" ++ text ++ "\n")


suite : Test
suite =
    describe "Translate.FrontEnd"
        [ describe "syntax:core-operator-chain"
            [ test "a mixed chain is refused, at its second operator" <|
                \_ -> body "x = a << b >> c" |> Expect.equal (Ok [ "syntax:core-operator-chain@3:12" ])
            , test "a chain of one associativity is fine" <|
                \_ -> body "x = a >> b >> c" |> Expect.equal (Ok [])
            , test "a chain inside a lambda, in a let, is checked" <|
                \_ -> body "x =\n    let\n        f = \\a -> a == 1 == True\n    in\n    f" |> Expect.equal (Ok [ "syntax:core-operator-chain@5:26" ])
            ]
        , describe "syntax:operator"
            [ test "an operator outside the figure is refused, in a chain or in parentheses" <|
                \_ -> body "x = a <?> b\n\ny = (<?>)" |> Expect.equal (Ok [ "syntax:operator@3:7", "syntax:operator@5:5" ])
            , test "an operator of the figure in parentheses is fine" <|
                \_ -> body "x = (+)" |> Expect.equal (Ok [])
            ]
        , describe "syntax:tuple-arity"
            [ test "a tuple of four is refused as an expression, a pattern and a type" <|
                \_ ->
                    body "f : ( Int, Int, Int, Int ) -> Int\nf ( a, b, c, d ) = ( a, b, c, d )"
                        |> Expect.equal (Ok [ "syntax:tuple-arity@3:5", "syntax:tuple-arity@4:3", "syntax:tuple-arity@4:20" ])
            , test "a tuple of three is fine" <|
                \_ -> body "f : ( Int, Int, Int ) -> Int\nf ( a, b, c ) = a" |> Expect.equal (Ok [])
            ]
        , describe "syntax:core-adjacent-items"
            [ test "a unit pattern with a gap is refused" <|
                \_ -> body "f ( ) = 1" |> Expect.equal (Ok [ "syntax:core-adjacent-items@3:3" ])
            , test "f () = 1 is fine" <|
                \_ -> body "f () = 1" |> Expect.equal (Ok [])
            , test "eco's parser rejects the other gaps" <|
                \_ ->
                    [ "x = ( )", "x = ( + )", "x : ( )\nx = x", "x = r. y", "x = - y" ]
                        |> List.map (body >> Result.toMaybe)
                        |> Expect.equal [ Nothing, Nothing, Nothing, Nothing, Nothing ]
            ]
        , describe "syntax:core-escape-unicode"
            [ test "a surrogate escape is refused in a character, a string and a pattern" <|
                \_ ->
                    body "c = '\\u{D800}'\n\ns = \"a\\u{DFFF}\"\n\nf x =\n    case x of\n        \"\\u{D83D}\" -> 1\n        _ -> 2"
                        |> Expect.equal (Ok [ "syntax:core-escape-unicode@3:5", "syntax:core-escape-unicode@5:5", "syntax:core-escape-unicode@9:9" ])
            , test "an escaped backslash before u{D800} is not an escape" <|
                \_ -> body "s = \"\\\\u{D800}\"" |> Expect.equal (Ok [])
            , test "a triple-quoted string over several lines is read whole" <|
                \_ -> body "s = \"\"\"one\ntwo \\u{D800}\nthree\"\"\"" |> Expect.equal (Ok [ "syntax:core-escape-unicode@3:5" ])
            , test "an astral escape and a non-surrogate escape are fine" <|
                \_ -> body "s = \"\\u{1F600}\\u{0041}\"\n\nc = '\\u{10FFFF}'" |> Expect.equal (Ok [])
            , test "the scanner itself" <|
                \_ ->
                    List.map FrontEnd.escapeProblem [ "'\\u{D800}'", "\"\\\\u{D800}\"", "\"\\u{110000}\"", "\"\\u{FFFF}\"" ]
                        |> Expect.equal [ True, False, True, False ]
            ]
        , describe "syntax:modules-header"
            [ test "a module without a header is refused" <|
                \_ -> check "x = 1\n" |> Expect.equal (Ok [ "syntax:modules-header@1:1" ])
            , test "module and port module headers are fine" <|
                \_ ->
                    [ check "module M exposing (x)\n\nx = 1\n", check "port module M exposing (x)\n\nport x : Int -> Cmd msg\n" ]
                        |> Expect.equal [ Ok [], Ok [] ]
            ]
        ]
