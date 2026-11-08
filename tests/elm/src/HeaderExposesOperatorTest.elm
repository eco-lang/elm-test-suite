module HeaderExposesOperatorTest exposing (main, (+))

{-| A module's header cannot expose an operator.

A Standard Definition of Elm?, restriction modules-no-operator-exposing: an item `(op)` occurs only
in the exposing list of an import; a module declares no operator, so it has none to expose.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-no-operator-exposing>

-}

-- TAGS: elm-spec, modules-no-operator-exposing
-- COMPILE-ERROR: an operator in a header's exposing list
-- CHECK: {{-- [A-Z ]+ -}}

import Html


main =
    Html.text (String.fromInt (1 + 2))
