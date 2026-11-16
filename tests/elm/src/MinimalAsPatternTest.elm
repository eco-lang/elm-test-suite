module MinimalAsPatternTest exposing (main)

{-| A layered pattern binds the whole value to its variable.

The simplest test of rules d-pat-as, s-pat-as of A Standard Definition of Elm?: `case 7 of _ as m ->
m`. <https://elm-test-suite.netlify.app/standard/rules/d-pat-as>

-}

-- TAGS: elm-spec, d-pat-as, s-pat-as
-- CHECK: testValue: 7

import Html exposing (text)


testValue =
    case 7 of
        _ as m ->
            m


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
