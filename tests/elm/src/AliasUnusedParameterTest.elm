module AliasUnusedParameterTest exposing (main)

{-| A type alias has no unused parameter.

A Standard Definition of Elm?, restriction modules-alias-tyvars: the parameters of an alias are
exactly the type variables of its type. `a` does not occur in `Int`. <https://elm-test-suite.netlify.app/standard/restrictions/modules-alias-tyvars>

-}

-- TAGS: elm-spec, modules-alias-tyvars
-- COMPILE-ERROR: a type alias with an unused parameter
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type alias Height a =
    Int


h : Height String
h =
    1


main =
    Html.text (String.fromInt h)
