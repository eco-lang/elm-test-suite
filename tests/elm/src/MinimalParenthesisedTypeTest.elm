module MinimalParenthesisedTypeTest exposing (main)

{-| An annotation with a parenthesised type.

The simplest test of rule s-ty-paren of A Standard Definition of Elm?: `testValue : (Int)`.
<https://elm-test-suite.netlify.app/standard/rules/s-ty-paren>

-}

-- TAGS: elm-spec, s-ty-paren
-- CHECK: testValue: 7

import Html exposing (text)


testValue : (Int)
testValue =
    7


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
