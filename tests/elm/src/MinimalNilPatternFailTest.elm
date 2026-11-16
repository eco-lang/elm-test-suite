module MinimalNilPatternFailTest exposing (main)

{-| The empty-list pattern fails on a list with an element.

The simplest test of rule d-atpat-nil-fail of A Standard Definition of Elm?: in `case [ 5 ] of [] ->
0 ; _ -> 1` the pattern `[]` fails, so the result is `1`.
<https://elm-test-suite.netlify.app/standard/rules/d-atpat-nil-fail>

-}

-- TAGS: elm-spec, d-atpat-nil-fail
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case [ 5 ] of
        [] ->
            0

        _ ->
            1


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
