module Translate.Directives exposing (Directives, Expectation(..), read)

{-| The directives of a test, read from its source text (they are comments, which the parser drops):
its tags, its CHECK and CHECK-NOT lines, its exit status, and whether it is refused because of a
directive (plans/elm-to-lean-translator.md, B.2).
-}

import Dict exposing (Dict)


type Expectation
    = Value String
    | NoValue


type alias Directives =
    { tags : List String
    , helper : Bool
    , expected : Dict String Expectation
    , labelsInOrder : List String
    , refusal : Maybe String
    }


prefix : String -> String -> Maybe String
prefix p line =
    if String.startsWith p line then
        Just (String.dropLeft (String.length p) line)

    else
        Nothing


read : String -> Directives
read source =
    let
        lines =
            String.lines source |> List.filter (String.startsWith "-- ")

        tags =
            lines
                |> List.filterMap (prefix "-- TAGS:")
                |> List.concatMap (String.split ",")
                |> List.map String.trim
                |> List.filter (not << String.isEmpty)

        exit =
            lines |> List.filterMap (prefix "-- EXIT:") |> List.map String.trim |> List.head

        has p =
            List.any (String.startsWith p) lines

        refusedBy =
            [ ( "-- COMPILE-ERROR:", "compile-error" )
            , ( "-- FLAGS:", "effects" )
            , ( "-- STDIN:", "effects" )
            , ( "-- STDIN-DELAY-MS:", "effects" )
            , ( "-- ENV:", "effects" )
            , ( "-- UNSETENV:", "effects" )
            , ( "-- CHECK-NEXT:", "checks:directive:CHECK-NEXT" )
            , ( "-- CHECK-SAME:", "checks:directive:CHECK-SAME" )
            , ( "-- CHECK-DAG:", "checks:directive:CHECK-DAG" )
            , ( "-- CHECK-LABEL:", "checks:directive:CHECK-LABEL" )
            ]
                |> List.filter (\( p, _ ) -> has p)
                |> List.map Tuple.second

        checkLines =
            lines |> List.filterMap (prefix "-- CHECK:") |> List.map String.trim

        checkNotLines =
            lines |> List.filterMap (prefix "-- CHECK-NOT:") |> List.map String.trim

        parsedChecks =
            checkLines
                |> List.map
                    (\text ->
                        if String.contains "{{" text then
                            Err "checks:regex"

                        else
                            case String.indexes ": " text of
                                at :: _ ->
                                    Ok ( String.left at text, Value (String.dropLeft (at + 2) text) )

                                [] ->
                                    Err "checks:unlabelled"
                    )

        parsedNots =
            checkNotLines
                |> List.map
                    (\text ->
                        if String.endsWith ":" text && exit == Just "1" then
                            Ok ( String.dropRight 1 text, NoValue )

                        else
                            Err "checks:check-not"
                    )

        exitRefusal =
            case exit of
                Nothing ->
                    []

                Just "0" ->
                    []

                Just "1" ->
                    if List.isEmpty checkNotLines then
                        [ "checks:exit" ]

                    else
                        []

                Just _ ->
                    [ "checks:exit" ]

        problems =
            refusedBy
                ++ List.filterMap
                    (\r ->
                        case r of
                            Err e ->
                                Just e

                            Ok _ ->
                                Nothing
                    )
                    (parsedChecks ++ parsedNots)
                ++ exitRefusal

        good =
            List.filterMap Result.toMaybe (parsedChecks ++ parsedNots)
    in
    { tags = tags
    , helper = has "-- HELPER:"
    , expected = Dict.fromList good
    , labelsInOrder = List.map Tuple.first good
    , refusal = List.head problems
    }
