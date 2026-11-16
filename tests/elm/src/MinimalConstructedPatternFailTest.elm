module MinimalConstructedPatternFailTest exposing (main)

{-| A constructor pattern with an argument fails on another constructor.

The simplest test of rule d-pat-con-fail of A Standard Definition of Elm?: in `case Nothing of Just
n -> n ; Nothing -> 0` the pattern `Just n` fails, so the result is `0`.
<https://elm-test-suite.netlify.app/standard/rules/d-pat-con-fail>

-}

-- TAGS: elm-spec, d-pat-con-fail
-- CHECK: testValue: 0

import Html exposing (text)


testValue =
    case Nothing of
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
