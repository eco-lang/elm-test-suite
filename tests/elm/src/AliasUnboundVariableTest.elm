module AliasUnboundVariableTest exposing (main)

{-| A type alias uses only its parameters.

A Standard Definition of Elm?, restriction modules-alias-tyvars: the parameters of an alias are
exactly the type variables of its type. `a` occurs in `List a` but is not a parameter.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-alias-tyvars>

-}

-- TAGS: elm-spec, modules-alias-tyvars
-- COMPILE-ERROR: a type alias with an unbound type variable
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type alias Items =
    List a


main =
    Html.text "done"
