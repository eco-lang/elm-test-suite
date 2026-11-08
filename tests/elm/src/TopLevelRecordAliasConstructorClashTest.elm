module TopLevelRecordAliasConstructorClashTest exposing (main)

{-| A record alias declares a constructor, which may not clash with a custom type's.

A Standard Definition of Elm?, restriction modules-constructors-distinct: a record alias `P` also
declares a constructor `P`, so it counts against a constructor `P` of a custom type.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-constructors-distinct>

-}

-- TAGS: elm-spec, modules-constructors-distinct
-- COMPILE-ERROR: a record alias constructor and a custom-type constructor with one name
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type Shape
    = P Int


type alias P =
    { x : Int, y : Int }


main =
    Html.text "done"
