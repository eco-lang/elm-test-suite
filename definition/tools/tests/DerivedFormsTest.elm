module DerivedFormsTest exposing (suite)

import Dict
import DerivedForms.Table as Table
import DerivedForms.Term exposing (..)
import DerivedForms.ToLatex as ToLatex
import DerivedForms.ToLean as ToLean
import Expect
import Regions
import Test exposing (Test, describe, test)


rows : Dict.Dict String Row
rows =
    Dict.fromList (List.map (\r -> ( r.label, r )) Table.rows)


rowNamed : String -> Row
rowNamed label =
    case Dict.get label rows of
        Just r ->
            r

        Nothing ->
            Debug.todo ("no row " ++ label)


suite : Test
suite =
    describe "Appendix A as data"
        [ test "the table has the book's 14 rows" <|
            \_ -> List.length Table.rows |> Expect.equal 14
        , test "df:infix prints as the book's row" <|
            \_ ->
                ToLatex.row rows (rowNamed "df:infix")
                    |> Expect.equal "\\dform{\\citelabel{df:infix}\\expm_1\\ \\opv\\ \\expm_2}\n      {\\kw{(}\\opv\\kw{)}\\ \\kw{(}\\expm_1\\kw{)}\\ \\kw{(}\\expm_2\\kw{)}}"
        , test "df:and prints the derived form of df:if with its arguments in place" <|
            \_ ->
                ToLatex.rowEquivalent rows (rowNamed "df:and")
                    |> Expect.equal "\\kw{if}\\ \\expm_1\\ \\kw{then}\\ \\expm_2\\ \\kw{else}\\ \\kw{Basics.False}"
        , test "df:list-pattern shows items 1, 2 and n" <|
            \_ ->
                ToLatex.rowEquivalent rows (rowNamed "df:list-pattern")
                    |> String.replace "\n       " " "
                    |> Expect.equal "\\kw{(}\\pat_1\\ \\kw{::}\\ \\kw{(}\\pat_2\\ \\kw{::}\\ \\cdots\\ \\kw{(}\\pat_n\\ \\kw{::}\\ \\kw{[ ]}\\kw{)}\\cdots\\kw{)}\\kw{)} \\quad (n\\geq 1)"
        , test "bin is printed as today's Lean definition" <|
            \_ ->
                ToLean.definitions [ rowNamed "df:infix" ]
                    |> Result.map (String.lines >> List.drop 1 >> String.join "\n")
                    |> Expect.equal (Ok "def bin (o : Op) (e1 : Exp) (e2 : Exp) : Exp :=\n  .app (.app (.atexp (.op o)) (.paren e1)) (.paren e2)")
        , test "rows come after the rows they use" <|
            \_ ->
                ToLean.orderedRows Table.rows
                    |> List.map .label
                    |> (\labels -> indexOf "df:if" labels < indexOf "df:and" labels && indexOf "df:infix" labels < indexOf "df:list" labels)
                    |> Expect.equal True
        , test "a class error in the table is rejected" <|
            \_ ->
                let
                    bad =
                        { label = "df:bad"
                        , block = Expressions
                        , derived = []
                        , equivalent = Template (TApp (TMeta (Plain Exp)) (TMeta (Indexed Exp 1)))
                        , condition = NoCondition
                        , lean =
                            Generated
                                { name = "bad"
                                , params = [ { name = "f", ref = Plain Exp }, { name = "e1", ref = Indexed Exp 1 } ]
                                , result = Exp
                                , seqParam = Nothing
                                , whenEmpty = Nothing
                                }
                        }
                in
                case ToLean.definitions [ bad ] of
                    Err _ ->
                        Expect.pass

                    Ok text ->
                        Expect.fail ("accepted: " ++ text)
        , test "a region is replaced between its markers" <|
            \_ ->
                Regions.replace { begin = "% B", end = "% E" } "new" "a\n% B x\nold\n% E\nz"
                    |> Expect.equal (Ok "a\n% B x\nnew\n% E\nz")
        , test "a missing marker is an error" <|
            \_ ->
                Regions.replace { begin = "% B", end = "% E" } "new" "a\n% B x\nold\nz"
                    |> Result.toMaybe
                    |> Expect.equal Nothing
        ]


indexOf : String -> List String -> Int
indexOf x xs =
    List.indexedMap Tuple.pair xs
        |> List.filter (\( _, y ) -> y == x)
        |> List.head
        |> Maybe.map Tuple.first
        |> Maybe.withDefault -1
