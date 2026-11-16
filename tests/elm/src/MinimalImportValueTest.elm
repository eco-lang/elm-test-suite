module MinimalImportValueTest exposing (main)

{-| A value exposed by one module and used in another.

The simplest test of rules dm-module, dm-header, dm-explist-items, dm-expitem-var, sm-explist-items,
p-stat-module of A Standard Definition of Elm?: the module MinimalHelperValue exposes `seven` by
name; the test imports and uses it. <https://elm-test-suite.netlify.app/standard/rules/dm-module>

-}

-- TAGS: elm-spec, dm-module, dm-header, dm-explist-items, dm-expitem-var, sm-explist-items
-- TAGS: p-stat-module
-- CHECK: testValue: 7

import Html exposing (text)
import MinimalHelperValue exposing (seven)

testValue =
    seven


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
