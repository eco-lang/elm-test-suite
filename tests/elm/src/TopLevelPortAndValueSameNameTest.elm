port module TopLevelPortAndValueSameNameTest exposing (main)

{-| A port and a top-level value may not have the same name.

A Standard Definition of Elm?, restriction modules-values-distinct: no top-level declaration may
bind the same variable twice by its value declarations and port declarations together.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-values-distinct>

-}

-- TAGS: elm-spec, modules-values-distinct
-- COMPILE-ERROR: a port and a value with one name
-- CHECK: {{-- [A-Z ]+ -}}

import Html


port send : String -> Cmd msg


send : String -> Cmd msg
send _ =
    Cmd.none


main =
    Html.text "done"
