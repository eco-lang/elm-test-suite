module TopLevelValueTwiceTest exposing (main)

{-| A module may not define the same top-level value twice.

A Standard Definition of Elm?, restriction modules-values-distinct: no top-level declaration may
bind the same variable twice. <https://elm-test-suite.netlify.app/standard/restrictions/modules-values-distinct>

-}

-- TAGS: elm-spec, modules-values-distinct
-- COMPILE-ERROR: a top-level value defined twice
-- CHECK: {{-- [A-Z ]+ -}}

import Html


x =
    1


x =
    2


main =
    Html.text (String.fromInt x)
