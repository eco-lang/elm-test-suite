module StandardA99RecordPatternFunctionTest exposing (main)

{-| A function bound by a record pattern in a `let`, applied at Int and at Float.

`{ h } = { h = \x -> x - 3 }` binds `h : number -> number`. The annotation fixes `h 5` at Int
(without it, `5` would default to Float) and `h 2.5` is at Float, so number specialisation makes
both copies. A Standard Definition of Elm?, ruling A99: the pattern row `{ h }` is a derived form of
`{ h = h }`, whose variable is a variable like any other, so a copy made by number specialisation
binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 2, -0.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: df:pattern-row-label
-- CHECK: testValue: (2,-0.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        { h } =
            { h = \x -> x - 3 }
    in
    ( h 5, h 2.5 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
