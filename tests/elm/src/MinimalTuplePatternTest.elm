module MinimalTuplePatternTest exposing (main)

{-| A tuple pattern matches the components of a pair.

The simplest test of rules d-atpat-tuple, s-atpat-tuple of A Standard Definition of Elm?: `case ( 1,
2 ) of ( a, b ) -> b` gives `2`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-tuple>

-}

-- TAGS: elm-spec, d-atpat-tuple, s-atpat-tuple
-- CHECK: testValue: 2

import Html exposing (text)


testValue =
    case ( 1, 2 ) of
        ( a, b ) ->
            b


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
