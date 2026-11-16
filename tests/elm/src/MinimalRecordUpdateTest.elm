module MinimalRecordUpdateTest exposing (main)

{-| A record update replaces the value of one field.

The simplest test of rules d-atexp-update, s-atexp-update of A Standard Definition of Elm?: `{ r | a
= 2 }` with `r` the record `{ a = 1 }`.
<https://elm-test-suite.netlify.app/standard/rules/d-atexp-update>

-}

-- TAGS: elm-spec, d-atexp-update, s-atexp-update
-- CHECK: testValue: { a = 2 }

import Html exposing (text)


r =
    { a = 1 }


testValue =
    { r | a = 2 }


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
