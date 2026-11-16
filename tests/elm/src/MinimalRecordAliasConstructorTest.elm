module MinimalRecordAliasConstructorTest exposing (main)

{-| A record type alias declares a constructor.

The simplest test of rule sm-typbind-record of A Standard Definition of Elm?: `type alias P = { a :
Int }` and the constructor application `P 1`.
<https://elm-test-suite.netlify.app/standard/rules/sm-typbind-record>

-}

-- TAGS: elm-spec, sm-typbind-record
-- CHECK: testValue: { a = 1 }

import Html exposing (text)


type alias P =
    { a : Int }


testValue =
    P 1


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
