module HeaderExposesConstructorByNameTest exposing (Two, main)

{-| A header cannot expose a constructor by name.

A Standard Definition of Elm?, restriction modules-header-exposing: an item `T` of a header names a
type, and the constructors of a custom type are exposed only by `T(..)` or `(..)`. `Two` is a
constructor of `T`, not a type. <https://elm-test-suite.netlify.app/standard/restrictions/modules-header-exposing>

-}

-- TAGS: elm-spec, modules-header-exposing
-- COMPILE-ERROR: a header exposing a constructor by name
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type T
    = One
    | Two


main =
    Html.text
        (case Two of
            One ->
                "one"

            Two ->
                "two"
        )
