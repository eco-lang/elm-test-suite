module MinimalEmptyListTest exposing (main)

{-| The empty list is a value.

The simplest test of rules d-atexp-nil, s-atexp-nil of A Standard Definition of Elm?: the expression
`[]` alone. <https://elm-test-suite.netlify.app/standard/rules/d-atexp-nil>

-}

-- TAGS: elm-spec, d-atexp-nil, s-atexp-nil
-- CHECK: testValue: []

import Html exposing (text)


testValue =
    []


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
