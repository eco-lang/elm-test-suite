module MinimalRecordTypeTest exposing (main)

{-| An annotation with a record type of one field.

The simplest test of rules s-ty-record, s-tyrow of A Standard Definition of Elm?: `testValue : { a :
Int }`, one type-expression row. <https://elm-test-suite.netlify.app/standard/rules/s-ty-record>

-}

-- TAGS: elm-spec, s-ty-record, s-tyrow
-- CHECK: testValue: { a = 1 }

import Html exposing (text)


testValue : { a : Int }
testValue =
    { a = 1 }


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
