module CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest exposing (..)

{-| Lambdas taken out of a tuple and a record by destructuring `let` patterns, put in a list and
applied in turn.

A local `applyAll` applies `[ (+1), (*2), (-3) ]` in turn starting from `5`, giving `6`, `12`,
then `9`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, d-atpat-tuple, d-atpat-record
-- CHECK: testValue: 9

import Basics exposing (..)
import Char exposing (Char)
import List exposing ((::))
import Maybe exposing (Maybe(..))
import Platform.Cmd as Cmd exposing (Cmd)
import Platform.Sub as Sub exposing (Sub)
import String exposing (String)
import Html


testValue : Int
testValue =
    let
        ( f, g ) =
            ( \x -> x + 1, \x -> x * 2 )

        { h } =
            { h = \x -> x - 3 }

        fs =
            [ f, g, h ]
    in
    applyAll fs 5


applyAll : List (Int -> Int) -> Int -> Int
applyAll fs acc =
    case fs of
        [] ->
            acc

        fn :: rest ->
            applyAll rest (fn acc)


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    Html.text "done"
