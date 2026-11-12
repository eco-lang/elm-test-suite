module StaticBasisTest exposing (suite)

{-| The reader of Appendix C (plans/lean-full-definition/step-07-classify.md, section 7), on rows
copied from the appendix.
-}

import Expect
import StaticBasis.Latex as L exposing (Ty(..))
import Test exposing (Test, describe, test)
import Translate.Basis as Basis


row : String -> List String
row =
    L.cells


ve : String -> Result String (List L.VEntry)
ve r =
    case row r of
        [ a, _, c ] ->
            L.parseVeRow a c

        _ ->
            Err "not three cells"


suite : Test
suite =
    describe "Appendix C"
        [ test "a simple VE row" <|
            \_ ->
                ve "\\kw{toFloat}\\citelabel{b:Basics.toFloat} & \\mapsto & (\\tInt \\rightarrow \\tFloat, \\isv)"
                    |> Result.map (List.map (\e -> ( e.name, e.scheme.body, e.status )))
                    |> Expect.equal (Ok [ ( "toFloat", TyFn (TyCon "Int" []) (TyCon "Float" []), "v" ) ])
        , test "a multi-name VE row gives each name the scheme" <|
            \_ ->
                ve "\\kw{round}\\citelabel{b:Basics.round},\\ \\kw{floor}\\citelabel{b:Basics.floor} & \\mapsto & (\\tFloat \\rightarrow \\tInt, \\isv)"
                    |> Result.map (List.map .name)
                    |> Expect.equal (Ok [ "round", "floor" ])
        , test "a continuation row is joined (max, min)" <|
            \_ ->
                [ row "\\kw{max}\\citelabel{b:Basics.max},\\ \\kw{min}\\citelabel{b:Basics.min} & \\mapsto & (\\forall\\mv{comparable}.\\,\\mv{comparable} \\rightarrow \\mv{comparable}"
                , row " & & \\phantom{(\\forall\\mv{comparable}.\\,}{} \\rightarrow \\mv{comparable}, \\isv)"
                ]
                    |> L.joinContinuations
                    |> List.map
                        (\r ->
                            case r of
                                [ a, _, c ] ->
                                    L.parseVeRow a c

                                _ ->
                                    Err "cells"
                        )
                    |> List.map (Result.map (List.map (.scheme >> .forall)))
                    |> Expect.equal [ Ok [ [ "comparable" ], [ "comparable" ] ] ]
        , test "the Bool TE row has two constructors" <|
            \_ ->
                L.parseTeRow "\\kw{Bool}\\citelabel{b:Basics.Bool}" "(\\tBool,\\ \\{\\kw{True} \\mapsto (\\tBool, \\isc),\\ \\kw{False} \\mapsto (\\tBool, \\isc)\\})"
                    |> Result.map (\te -> ( te.typeName, List.map (\c -> ( c.name, c.status )) te.ve ))
                    |> Expect.equal (Ok ( "Bool", [ ( "True", "c" ), ( "False", "c" ) ] ))
        , test "the Order TE row with its phantom continuation has three constructors" <|
            \_ ->
                [ row "\\kw{Order}\\citelabel{b:Basics.Order} & \\mapsto & (\\sbtOrder,\\ \\{\\kw{LT} \\mapsto (\\sbtOrder, \\isc),\\ \\kw{EQ} \\mapsto (\\sbtOrder, \\isc),"
                , row " & & \\phantom{(\\sbtOrder,\\ \\{}\\kw{GT} \\mapsto (\\sbtOrder, \\isc)\\})"
                ]
                    |> L.joinContinuations
                    |> List.map
                        (\r ->
                            case r of
                                [ a, _, c ] ->
                                    L.parseTeRow a c |> Result.map (.ve >> List.map .name)

                                _ ->
                                    Err "cells"
                        )
                    |> Expect.equal [ Ok [ "LT", "EQ", "GT" ] ]
        , test "the worker row, a closed record of three fields over five lines" <|
            \_ ->
                [ row "\\kw{worker}\\citelabel{b:Platform.worker} & \\mapsto & (\\forall\\mv{flags}\\,\\mv{model}\\,\\mv{msg}."
                , row " & & \\quad\\{\\kw{init} \\mapsto \\mv{flags} \\rightarrow (\\mv{model}, \\mv{msg}\\,\\sbtCmd)\\tTuple{2},"
                , row " & & \\quad\\phantom{\\{}\\kw{update} \\mapsto \\mv{msg} \\rightarrow \\mv{model} \\rightarrow (\\mv{model}, \\mv{msg}\\,\\sbtCmd)\\tTuple{2},"
                , row " & & \\quad\\phantom{\\{}\\kw{subscriptions} \\mapsto \\mv{model} \\rightarrow \\mv{msg}\\,\\sbtSub\\}"
                , row " & & \\quad{} \\rightarrow (\\mv{flags}, \\mv{model}, \\mv{msg})\\sbtProgram,\\ \\isv)"
                ]
                    |> L.joinContinuations
                    |> List.map
                        (\r ->
                            case r of
                                [ a, _, c ] ->
                                    L.parseVeRow a c
                                        |> Result.map
                                            (List.map
                                                (\e ->
                                                    case e.scheme.body of
                                                        TyFn (TyRecord fs) (TyCon "Program" _) ->
                                                            List.map Tuple.first fs

                                                        _ ->
                                                            []
                                                )
                                            )

                                _ ->
                                    Err "cells"
                        )
                    |> Expect.equal [ Ok [ [ "init", "update", "subscriptions" ] ] ]
        , test "an operator row pairs + and - with add and sub; ::* is declared by List" <|
            \_ ->
                Expect.all
                    [ \_ ->
                        L.parseOpRow "\\kw{+},\\ \\kw{-}" "\\kw{add}\\citelabel{b:Basics.add},\\ \\kw{sub}\\citelabel{b:Basics.sub}" "(\\forall\\mv{number}.\\,\\mv{number} \\rightarrow \\mv{number} \\rightarrow \\mv{number}, \\isv)"
                            |> Result.map (List.map (\( o, e, star ) -> ( o, e.name, star )))
                            |> Expect.equal (Ok [ ( "+", "add", False ), ( "-", "sub", False ) ])
                    , \_ ->
                        L.parseOpRow "\\kw{::}^{*}" "\\kw{::}\\citealso{b:List}" "(\\forall\\mv{a}.\\,\\mv{a} \\rightarrow \\mv{a}\\,\\tList \\rightarrow \\mv{a}\\,\\tList, \\isc)"
                            |> Result.map (List.map (\( o, _, star ) -> ( o, star )))
                            |> Expect.equal (Ok [ ( "::", True ) ])
                    ]
                    ()
        , test "a heading naming two modules is read as both" <|
            \_ ->
                L.tokenize "\\multicolumn{3}{|l|}{\\kw{Json.Encode}\\ \\text{and}\\ \\kw{Json.Decode}}"
                    |> Result.toMaybe
                    |> Expect.equal Nothing
        , test "an arity mismatch is an error" <|
            \_ ->
                ve "\\kw{x} & \\mapsto & ((\\tInt, \\tInt)\\tList, \\isv)"
                    |> Expect.err
        , test "an unknown macro in a type is an error" <|
            \_ ->
                ve "\\kw{x} & \\mapsto & (\\tFoo, \\isv)"
                    |> Expect.err
        , test "Basis.valueNames are all answered by value" <|
            \_ ->
                Basis.valueNames
                    |> List.filter (\x -> Basis.value "" x == Nothing)
                    |> Expect.equal []
        ]
