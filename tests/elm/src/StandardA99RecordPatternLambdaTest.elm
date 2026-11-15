module StandardA99RecordPatternLambdaTest exposing (main)

{-| A record pattern in a lambda inside a `let` binding that is copied.

`( f, k ) = ( \{ m } -> m + 1, 2 )` binds `f : { a | m : number } -> number` and `k : number1`. `f`
is used at Int and at Float, so number specialisation copies the binding. The record pattern in the
lambda binds `m` only inside the lambda: a copy renames `f` and `k`, the variables the binding
binds, and not `m`. A Standard Definition of Elm?, ruling A99: the pattern row `{ m }` is a derived
form of `{ m = m }`, whose variable is a variable like any other, so a copy made by number
specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 3, 3.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: s-atpat-tuple, d-atpat-tuple, df:pattern-row-label
-- CHECK: testValue: (3,3.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        ( f, k ) =
            ( \{ m } -> m + 1, 2 )
    in
    ( f { m = k // 1 }, f { m = 2.5 } )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
