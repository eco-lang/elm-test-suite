module ImportUnknownOperatorTest exposing (main)

{-| An import cannot name an operator its module does not have.

A Standard Definition of Elm?, rule sm-item-op: the item `(op)` elaborates only if the module
declares the operator. `Basics` has no `<+>`. <https://elm-test-suite.netlify.app/standard/rules/sm-item-op>

-}

-- TAGS: elm-spec, sm-item-op
-- COMPILE-ERROR: an import of an operator the module does not have
-- CHECK: {{-- [A-Z ]+ -}}

import Basics exposing ((<+>))
import Html


main =
    Html.text "done"
