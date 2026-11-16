module MinimalUnitPatternTest exposing (main)

{-| The unit pattern matches the unit value.

The simplest test of rules d-atpat-unit, s-atpat-unit of A Standard Definition of Elm?: `case () of
() -> 1`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-unit>

-}

-- TAGS: elm-spec, d-atpat-unit, s-atpat-unit
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case () of
        () ->
            1


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
