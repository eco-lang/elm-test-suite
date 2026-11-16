module MinimalConsPatternFailTest exposing (main)

{-| A list construction pattern fails on the empty list.

The simplest test of rule d-pat-cons-fail of A Standard Definition of Elm?: in `case [] of x :: _ ->
x ; [] -> "none"` the pattern `x :: _` fails, so the result is `"none"`.
<https://elm-test-suite.netlify.app/standard/rules/d-pat-cons-fail>

-}

-- TAGS: elm-spec, d-pat-cons-fail
-- CHECK: testValue: "none"

import Html exposing (text)


testValue =
    case [] of
        x :: _ ->
            x

        [] ->
            "none"


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
