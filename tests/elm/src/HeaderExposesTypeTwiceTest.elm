module HeaderExposesTypeTwiceTest exposing (T, T(..), main)

{-| A header cannot expose a type both closed and with its constructors.

A Standard Definition of Elm?, restriction modules-exposing-distinct: no two items of the exposing
list of a header may have the same identifier, so `T` and `T(..)` do not both occur.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-exposing-distinct>

-}

-- TAGS: elm-spec, modules-exposing-distinct
-- COMPILE-ERROR: a header exposing T and T(..)
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type T
    = T Int


main =
    Html.text "done"
