module MinimalRecordTest exposing (main)

{-| A record expression with one field.

The simplest test of rules d-atexp-record, d-exprow-field, s-atexp-record, s-exprow of A Standard
Definition of Elm?: the record `{ a = 1 }`, one expression row.
<https://elm-test-suite.netlify.app/standard/rules/d-atexp-record>

-}

-- TAGS: elm-spec, d-atexp-record, d-exprow-field, s-atexp-record, s-exprow
-- CHECK: testValue: { a = 1 }

import Html exposing (text)


testValue =
    { a = 1 }


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
