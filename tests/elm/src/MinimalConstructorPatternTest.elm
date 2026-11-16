module MinimalConstructorPatternTest exposing (main)

{-| A constructor pattern without arguments matches its constructor.

The simplest test of rules d-atpat-con, s-atpat-con of A Standard Definition of Elm?: `case True of
True -> 1 ; False -> 0` gives `1`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-con>

-}

-- TAGS: elm-spec, d-atpat-con, s-atpat-con
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case True of
        True ->
            1

        False ->
            0


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
