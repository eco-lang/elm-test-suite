module MinimalRecordPatternTest exposing (main)

{-| A record pattern binds the field it names.

The simplest test of rules d-atpat-record, s-atpat-record, d-patrow-field, s-patrow of A Standard
Definition of Elm?: `case { a = 1 } of { a } -> a`.
<https://elm-test-suite.netlify.app/standard/rules/d-atpat-record>

-}

-- TAGS: elm-spec, d-atpat-record, s-atpat-record, d-patrow-field, s-patrow
-- CHECK: testValue: 1

import Html exposing (text)


testValue =
    case { a = 1 } of
        { a } ->
            a


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
