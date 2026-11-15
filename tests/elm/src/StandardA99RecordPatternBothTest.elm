module StandardA99RecordPatternBothTest exposing (main)

{-| A variable bound by a record pattern in a `let`, used at Int and at Float.

`{ n } = { n = 7 }` binds `n : number`, used at Int in `n // 2` and at Float in `n / 2`. Number
specialisation makes a copy of the binding for each. A Standard Definition of Elm?, ruling A99: the
pattern row `{ n }` is a derived form of `{ n = n }`, whose variable is a variable like any other,
so a copy made by number specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 3, 3.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: df:pattern-row-label
-- CHECK: testValue: (3,3.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        { n } =
            { n = 7 }
    in
    ( n // 2, n / 2 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
