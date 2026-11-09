module RecordUpdateNoFieldsTest exposing (main)

{-| A record update with no fields, `{ r | }`, is rejected.

A Standard Definition of Elm?, restriction core-record-update-form: in a record update
`{ var | exprow }` at least one expression row follows `|`. <https://elm-test-suite.netlify.app/standard/restrictions/core-record-update-form>

-}

-- TAGS: elm-spec, core-record-update-form
-- COMPILE-ERROR: a record update without fields
-- CHECK: {{-- [A-Z ]+ -}}

import Html


update : { key : Int } -> { key : Int }
update r =
    { r | }


main =
    let
        _ =
            Debug.log "key" (update { key = 1 }).key
    in
    Html.text "done"
