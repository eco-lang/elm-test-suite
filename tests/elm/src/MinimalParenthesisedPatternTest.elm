module MinimalParenthesisedPatternTest exposing (main)

{-| A parenthesised pattern matches as the pattern it encloses.

The simplest test of rules d-atpat-paren, s-atpat-paren of A Standard Definition of Elm?: `case 7 of
(n) -> n`. <https://elm-test-suite.netlify.app/standard/rules/d-atpat-paren>

-}

-- TAGS: elm-spec, d-atpat-paren, s-atpat-paren
-- CHECK: testValue: 7

import Html exposing (text)


testValue =
    case 7 of
        (n) ->
            n


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
