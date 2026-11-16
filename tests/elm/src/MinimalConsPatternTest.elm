module MinimalConsPatternTest exposing (main)

{-| A list construction pattern matches a non-empty list.

The simplest test of rules d-pat-cons, s-pat-cons of A Standard Definition of Elm?: `case [ 1 ] of x
:: _ -> x ; [] -> 0` gives `1`. <https://elm-test-suite.netlify.app/standard/rules/d-pat-cons>

-}

-- TAGS: elm-spec, d-pat-cons, s-pat-cons
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case [ 1 ] of
        x :: _ ->
            x

        [] ->
            0


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
