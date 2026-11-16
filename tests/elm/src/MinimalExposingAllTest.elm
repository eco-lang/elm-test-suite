module MinimalExposingAllTest exposing (main)

{-| A module that exposes everything with `(..)`.

The simplest test of rule dm-explist-all of A Standard Definition of Elm?: MinimalHelperAll is
declared `exposing (..)`, and its value `eight` is used here.
<https://elm-test-suite.netlify.app/standard/rules/dm-explist-all>

-}

-- TAGS: elm-spec, dm-explist-all
-- CHECK: testValue: 8

import Html exposing (text)
import MinimalHelperAll exposing (eight)

testValue =
    eight


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
