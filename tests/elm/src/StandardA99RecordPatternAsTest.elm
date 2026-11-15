module StandardA99RecordPatternAsTest exposing (main)

{-| A record pattern under `as` in a `let` binding.

`({ n } as r) = { n = 7 }` binds `n : number` and `r : { n : number }`, with one `number`. `n // 2`
is at Int and `r.n / 2` at Float, so number specialisation copies the binding at both, renaming `n`
and `r` in each. A Standard Definition of Elm?, ruling A99: the pattern row `{ n }` is a derived
form of `{ n = n }`, whose variable is a variable like any other, so a copy made by number
specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 3, 3.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers, s-pat-as
-- TAGS: d-pat-as, df:pattern-row-label
-- CHECK: testValue: (3,3.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        ({ n } as r) =
            { n = 7 }
    in
    ( n // 2, r.n / 2 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
