module MinimalConstantPatternTest exposing (main)

{-| A constant pattern matches the constant it spells.

The simplest test of rules d-atpat-scon, s-atpat-scon of A Standard Definition of Elm?: `case 1 of 1
-> 10 ; _ -> 20` gives `10`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-scon>

-}

-- TAGS: elm-spec, d-atpat-scon, s-atpat-scon
-- CHECK: testValue: 10

import Html exposing (text)


testValue =
    case 1 of
        1 ->
            10

        _ ->
            20


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
