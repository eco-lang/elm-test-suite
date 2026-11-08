module TopLevelTypeAndAliasSameNameTest exposing (main)

{-| A custom type and a type alias may not have the same name.

A Standard Definition of Elm?, restriction modules-types-distinct: custom types and aliases share
one name space, and no module declares a type name twice. <https://elm-test-suite.netlify.app/standard/restrictions/modules-types-distinct>

-}

-- TAGS: elm-spec, modules-types-distinct
-- COMPILE-ERROR: a custom type and an alias with one name
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type A
    = A Int


type alias A =
    Int


main =
    Html.text "done"
