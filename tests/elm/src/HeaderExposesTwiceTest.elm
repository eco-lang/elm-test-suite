module HeaderExposesTwiceTest exposing (main, main)

{-| No item may occur twice in a header's exposing list.

A Standard Definition of Elm?, restriction modules-exposing-distinct: no two items of the exposing
list of a header may have the same identifier. <https://elm-test-suite.netlify.app/standard/restrictions/modules-exposing-distinct>

-}

-- TAGS: elm-spec, modules-exposing-distinct
-- COMPILE-ERROR: a header exposing main twice
-- CHECK: {{-- [A-Z ]+ -}}

import Html


main =
    Html.text "done"
