module MinimalVariableTest exposing (main)

{-| A top-level variable denotes the value of its definition.

The simplest test of rules d-atexp-var, s-atexp-longvar, dm-topdec-seq of A Standard Definition of
Elm?: the variable `seven`, bound by the declaration before the one that uses it, looked up in the
environment that declaration made. <https://elm-test-suite.netlify.app/standard/rules/d-atexp-var>

-}

-- TAGS: elm-spec, d-atexp-var, s-atexp-longvar, dm-topdec-seq
-- CHECK: testValue: 7

import Html exposing (text)


seven =
    7


testValue =
    seven


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
