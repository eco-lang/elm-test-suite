module MinimalRowVariableTest exposing (main)

{-| An annotation with an extensible record type.

The simplest test of rules s-ty-rowvar, s-ty-openrecord of A Standard Definition of Elm?: `getA : {
r | a : Int } -> Int` is applied to a record with a further field.
<https://elm-test-suite.netlify.app/standard/rules/s-ty-rowvar>

-}

-- TAGS: elm-spec, s-ty-rowvar, s-ty-openrecord
-- CHECK: testValue: 1

import Html exposing (text)


getA : { r | a : Int } -> Int
getA { a } =
    a


testValue =
    getA { a = 1, b = 2 }


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
