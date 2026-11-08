module ImportAliasOpenItemTest exposing (main)

{-| An import cannot name a type alias with `(..)`.

A Standard Definition of Elm?, rule sm-item-opentype: the item `T(..)` elaborates only for a custom
type. `Point` is a record alias. <https://elm-test-suite.netlify.app/standard/rules/sm-item-opentype>

-}

-- TAGS: elm-spec, sm-item-opentype
-- COMPILE-ERROR: an import of an alias with (..)
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ModuleExposingHelper exposing (Point(..))


main =
    Html.text "done"
