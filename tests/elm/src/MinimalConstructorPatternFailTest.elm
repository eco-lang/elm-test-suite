module MinimalConstructorPatternFailTest exposing (main)

{-| A constructor pattern without arguments fails on another constructor.

The simplest test of rule d-atpat-con-fail of A Standard Definition of Elm?: in `case False of True
-> 1 ; False -> 0` the pattern `True` fails, so the result is `0`.
<https://elm-test-suite.netlify.app/standard/rules/d-atpat-con-fail>

-}

-- TAGS: elm-spec, d-atpat-con-fail
-- CHECK: testValue: 0

import Html exposing (text)


testValue =
    case False of
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
