module CustomTypeUnboundRowVariableTest exposing (main)

{-| The extension variable of a record type in a constructor is a parameter of the type.

A Standard Definition of Elm?, restriction modules-custom-type-tyvars: every type variable occurring
in the constructors, including the extension variable of a record type, is a parameter. `r` is not.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-custom-type-tyvars>

-}

-- TAGS: elm-spec, modules-custom-type-tyvars
-- COMPILE-ERROR: a custom type whose constructor uses an unbound extension variable
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type Holder
    = Holder { r | name : String }


main =
    Html.text "done"
