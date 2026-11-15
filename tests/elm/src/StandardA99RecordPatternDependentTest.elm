module StandardA99RecordPatternDependentTest exposing (main)

{-| A `let` definition that uses a variable bound by a record pattern.

`{ n } = { n = 7 }` binds `n : number`, and `m = n + 2` makes `m : number` from it. `m // 2` is at
Int and `m / 2` at Float, so number specialisation copies `m` at both, and each copy of `m` needs
the copy of the record binding at its type. A Standard Definition of Elm?, ruling A99: the pattern
row `{ n }` is a derived form of `{ n = n }`, whose variable is a variable like any other, so a copy
made by number specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 4, 4.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: df:pattern-row-label
-- CHECK: testValue: (4,4.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        { n } =
            { n = 7 }

        m =
            n + 2
    in
    ( m // 2, m / 2 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
