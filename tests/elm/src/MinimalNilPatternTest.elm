module MinimalNilPatternTest exposing (main)

{-| The empty-list pattern matches the empty list.

The simplest test of rules d-atpat-nil, s-atpat-nil of A Standard Definition of Elm?: `case [] of []
-> 1 ; _ -> 2` gives `1`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-nil>

-}

-- TAGS: elm-spec, d-atpat-nil, s-atpat-nil
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case [] of
        [] ->
            1

        _ ->
            2


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
