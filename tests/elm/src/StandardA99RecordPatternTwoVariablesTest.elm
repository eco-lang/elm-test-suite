module StandardA99RecordPatternTwoVariablesTest exposing (main)

{-| Two variables of one record pattern, with independent `number` types, used at opposite types.

`{ a, b } = { a = 5, b = 3 }` binds `a : number` and `b : number1`. The first pair uses `a` at Int
and `b` at Float, the second the other way round, so number specialisation makes copies for (Int,
Float) and (Float, Int), each binding new variables to fields `a` and `b`. A Standard Definition of
Elm?, ruling A99: the pattern row `{ a, b }` is a derived form of `{ a = a, b = b }`, whose variable
is a variable like any other, so a copy made by number specialisation binds a new variable to the
same field. <https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( ( 2, 1.5 ), ( 2.5, 1 ) )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: df:pattern-row-label
-- CHECK: testValue: ((2,1.5),(2.5,1))

import Html exposing (text)


testValue : ( ( Int, Float ), ( Float, Int ) )
testValue =
    let
        { a, b } =
            { a = 5, b = 3 }
    in
    ( ( a // 2, b / 2 ), ( a / 2, b // 2 ) )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
