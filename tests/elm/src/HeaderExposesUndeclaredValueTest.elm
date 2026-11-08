module HeaderExposesUndeclaredValueTest exposing (main, missing)

{-| A header exposes only values the module declares.

A Standard Definition of Elm?, restriction modules-header-exposing: each item `x` of a header's
exposing list is bound by a value or port declaration of the module. `missing` is not.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-header-exposing>

-}

-- TAGS: elm-spec, modules-header-exposing
-- COMPILE-ERROR: a header exposing an undeclared value
-- CHECK: {{-- [A-Z ]+ -}}

import Html


main =
    Html.text "done"
