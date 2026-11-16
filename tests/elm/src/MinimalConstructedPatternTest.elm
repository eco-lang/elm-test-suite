module MinimalConstructedPatternTest exposing (main)

{-| A constructor pattern with an argument matches and binds the argument.

The simplest test of rules d-pat-con, s-pat-con of A Standard Definition of Elm?: `case Just 3 of
Just n -> n ; Nothing -> 0` gives `3`. <https://elm-test-suite.netlify.app/standard/rules/d-pat-con>

-}

-- TAGS: elm-spec, d-pat-con, s-pat-con
-- CHECK: testValue: 3

import Html exposing (text)


testValue =
    case Just 3 of
        Just n ->
            n

        Nothing ->
            0


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
