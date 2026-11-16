module MinimalUnitTest exposing (main)

{-| The unit expression has the unit type and value.

The simplest test of rules d-atexp-unit, s-atexp-unit, s-ty-unit of A Standard Definition of Elm?:
`()` annotated with the unit type `()`.
<https://elm-test-suite.netlify.app/standard/rules/d-atexp-unit>

-}

-- TAGS: elm-spec, d-atexp-unit, s-atexp-unit, s-ty-unit
-- CHECK: testValue: ()

import Html exposing (text)


testValue : ()
testValue =
    ()


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
