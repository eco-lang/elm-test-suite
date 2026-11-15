module StandardA99RecordPatternInTopCopyTest exposing (main)

{-| A record pattern in a `let` inside a top-level value that is itself copied.

`v` is `number`, used at Int in `v // 4` and at Float in `v / 4`. Number specialisation copies `v`
at each type, from the outside in; inside each copy the `let` binding `{ n } = { n = 6 }` is used at
that copy's type and is copied in turn. A Standard Definition of Elm?, ruling A99: the pattern row
`{ n }` is a derived form of `{ n = n }`, whose variable is a variable like any other, so a copy
made by number specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 1, 1.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: df:pattern-row-label
-- CHECK: testValue: (1,1.5)

import Html exposing (text)


v =
    let
        { n } =
            { n = 6 }
    in
    n


testValue : ( Int, Float )
testValue =
    ( v // 4, v / 4 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
