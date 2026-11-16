module MinimalConstantTest exposing (main)

{-| An integer constant is a value.

The simplest test of rules d-exp-atexp, s-exp-atexp of A Standard Definition of Elm?: an atomic
expression, here the constant `7`, used as an expression.
<https://elm-test-suite.netlify.app/standard/rules/d-exp-atexp>

-}

-- TAGS: elm-spec, d-exp-atexp, s-exp-atexp
-- CHECK: testValue: 7

import Html exposing (text)


testValue =
    7


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
