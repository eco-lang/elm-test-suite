module MinimalParenthesesTest exposing (main)

{-| A parenthesised expression has the value of what it encloses.

The simplest test of rules d-atexp-paren, s-atexp-paren of A Standard Definition of Elm?: the
expression `(7)`. <https://elm-test-suite.netlify.app/standard/rules/d-atexp-paren>

-}

-- TAGS: elm-spec, d-atexp-paren, s-atexp-paren
-- CHECK: testValue: 7

import Html exposing (text)


testValue =
    (7)


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
