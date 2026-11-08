module CustomTypeUnboundVariableTest exposing (main)

{-| A custom type's constructors use only the type's parameters.

A Standard Definition of Elm?, restriction modules-custom-type-tyvars: every type variable occurring
in the constructors of a custom type is one of its parameters. `a` is not.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-custom-type-tyvars>

-}

-- TAGS: elm-spec, modules-custom-type-tyvars
-- COMPILE-ERROR: a custom type whose constructor uses an unbound type variable
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type Box
    = Box a


main =
    Html.text "done"
