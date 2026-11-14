module FixityTest exposing (suite)

{-| Grouping operator chains by `fig:core-fixities` (plans/eco-parser.md, E5, step 3).
-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Dict
import Expect
import Test exposing (Test, describe, test)
import Translate.Fixity as Fixity
import Translate.Parse as Parse


{-| The body of `x = <text>`, grouped and written back with every application in parentheses, or
the reason of its refusal.
-}
grouped : String -> Result String String
grouped text =
    case Parse.parse ("module M exposing (x)\n\nx = " ++ text ++ "\n") |> Result.map Parse.functions of
        Ok [ f ] ->
            show f.body

        Ok _ ->
            Err "not one function"

        Err e ->
            Err ("parse " ++ e)


show : Src.Expr -> Result String String
show (A.At _ e) =
    case e of
        Src.Binops first rest last ->
            Fixity.group first rest last
                |> Result.mapError .reason
                |> Result.andThen showTree

        Src.Var _ x ->
            Ok x

        Src.Parens ( _, x ) ->
            show x

        _ ->
            Ok "?"


showTree : Fixity.Tree -> Result String String
showTree t =
    case t of
        Fixity.Operand x ->
            show x

        Fixity.Apply a ->
            Result.map2 (\l r -> "(" ++ l ++ " " ++ a.op ++ " " ++ r ++ ")") (showTree a.left) (showTree a.right)


suite : Test
suite =
    describe "Translate.Fixity"
        [ test "|> groups to the left" <|
            \_ -> grouped "a |> f |> g" |> Expect.equal (Ok "((a |> f) |> g)")
        , test ":: and ++ group to the right" <|
            \_ ->
                ( grouped "a :: b :: c", grouped "a ++ b ++ c", grouped "a ++ b :: c" )
                    |> Expect.equal ( Ok "(a :: (b :: c))", Ok "(a ++ (b ++ c))", Ok "(a ++ (b :: c))" )
        , test "* binds more tightly than +; - groups to the left" <|
            \_ ->
                ( grouped "a + b * c", grouped "a * b + c", grouped "a - b - c" )
                    |> Expect.equal ( Ok "(a + (b * c))", Ok "((a * b) + c)", Ok "((a - b) - c)" )
        , test "a chain of all levels" <|
            \_ -> grouped "a || b && c == d + e * f ^ g ^ h" |> Expect.equal (Ok "(a || (b && (c == (d + (e * (f ^ (g ^ h)))))))")
        , test "a comparison on each side of && is fine" <|
            \_ -> grouped "a == b && c < d" |> Expect.equal (Ok "((a == b) && (c < d))")
        , test "<< and >> together are refused" <|
            \_ -> grouped "a << b >> c" |> Expect.equal (Err "syntax:core-operator-chain")
        , test "two non-associative operators of one precedence are refused" <|
            \_ ->
                ( grouped "1 < 2 == True", grouped "a == b == c" )
                    |> Expect.equal ( Err "syntax:core-operator-chain", Err "syntax:core-operator-chain" )
        , test "|> and <| together are refused" <|
            \_ -> grouped "a |> f <| b" |> Expect.equal (Err "syntax:core-operator-chain")
        , test "parentheses make a new chain" <|
            \_ -> grouped "a == (b == c)" |> Expect.equal (Ok "(a == (b == c))")
        , test "an operator outside the figure is refused" <|
            \_ -> grouped "a <?> b" |> Expect.equal (Err "syntax:operator")
        , test "the table is the figure's twenty operators" <|
            \_ -> Expect.equal 20 (Dict.size Fixity.table)
        ]
