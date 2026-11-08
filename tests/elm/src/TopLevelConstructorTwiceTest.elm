module TopLevelConstructorTwiceTest exposing (main)

{-| Two custom types may not declare the same constructor.

A Standard Definition of Elm?, restriction modules-constructors-distinct: no module may declare the
same constructor twice. <https://elm-test-suite.netlify.app/standard/restrictions/modules-constructors-distinct>

-}

-- TAGS: elm-spec, modules-constructors-distinct
-- COMPILE-ERROR: a constructor declared by two types
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type A
    = C Int


type B
    = C String


main =
    Html.text "done"
