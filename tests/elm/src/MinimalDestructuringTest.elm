module MinimalDestructuringTest exposing (main)

{-| A let definition by a tuple pattern.

The simplest test of rules d-valbind-pat, s-valbind-pat of A Standard Definition of Elm?: `let ( a,
b ) = ( 1, 2 ) in b` gives `2`. <https://elm-test-suite.netlify.app/standard/rules/d-valbind-pat>

-}

-- TAGS: elm-spec, d-valbind-pat, s-valbind-pat
-- CHECK: testValue: 2

import Html exposing (text)


testValue =
    let
        ( a, b ) =
            ( 1, 2 )
    in
    b


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
