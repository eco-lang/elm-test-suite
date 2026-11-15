module StandardA99RecordPatternInTupleTest exposing (main)

{-| A record pattern inside the tuple pattern of a `let` binding.

`( { p }, q ) = ( { p = 9 }, 4 )` binds `p : number` and `q : number1`. `p // q` is at Int and `p /
q` at Float, so number specialisation copies the binding at Int and at Float, each copy renaming the
variable of the nested pattern row. A Standard Definition of Elm?, ruling A99: the pattern row `{ p
}` is a derived form of `{ p = p }`, whose variable is a variable like any other, so a copy made by
number specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 2, 2.25 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: s-atpat-tuple, d-atpat-tuple, df:pattern-row-label
-- CHECK: testValue: (2,2.25)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        ( { p }, q ) =
            ( { p = 9 }, 4 )
    in
    ( p // q, p / q )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
