module MinimalExposingAliasTest exposing (main)

{-| A module that exposes a record type alias.

The simplest test of rule dm-expitem-alias of A Standard Definition of Elm?: MinimalHelperAlias
exposes `P`, and its constructor builds a record here.
<https://elm-test-suite.netlify.app/standard/rules/dm-expitem-alias>

-}

-- TAGS: elm-spec, dm-expitem-alias
-- CHECK: testValue: { a = 1 }

import Html exposing (text)
import MinimalHelperAlias exposing (P)

testValue =
    P 1


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
