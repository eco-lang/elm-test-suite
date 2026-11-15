module StandardA99RecordPatternSharedVariableTest exposing (main)

{-| Two variables of one record pattern that share one `number` type.

The function makes a record with both fields equal to its argument, so `a` and `b` both have type
`number`, the same variable. Using `a` at Int and `b` at Float needs the copies at Int and at Float
of the whole binding. A Standard Definition of Elm?, ruling A99: the pattern row `{ a, b }` is a
derived form of `{ a = a, b = b }`, whose variable is a variable like any other, so a copy made by
number specialisation binds a new variable to the same field.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

Elm 0.19.1 gives `( 2, 2.5 )`.

-}

-- TAGS: elm-spec, s-valbind-pat, d-valbind-pat, s-atpat-record, d-atpat-record, s-patrow
-- TAGS: d-patrow-field, s-dec-group, s-atexp-scon, d-atexp-scon, sec:dynamic-core-numbers
-- TAGS: s-exp-app, d-app-closure, df:pattern-row-label
-- CHECK: testValue: (2,2.5)

import Html exposing (text)


testValue : ( Int, Float )
testValue =
    let
        { a, b } =
            (\x -> { a = x, b = x }) 5
    in
    ( a // 2, b / 2 )


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
