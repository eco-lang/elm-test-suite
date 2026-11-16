module MinimalLetTest exposing (main)

{-| A let expression with one definition.

The simplest test of rules d-atexp-let, s-atexp-let, d-dec-nonrec, d-valbind-var of A Standard
Definition of Elm?: `let x = 1 in x`, whose declaration is not recursive.
<https://elm-test-suite.netlify.app/standard/rules/d-atexp-let>

-}

-- TAGS: elm-spec, d-atexp-let, s-atexp-let, d-dec-nonrec, d-valbind-var
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    let
        x =
            1
    in
    x


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
