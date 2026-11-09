module ModuleHeaderMissingImportedTest exposing (main)

{-| A module that imports a file with no `module` line is rejected.

`ModuleHeaderMissingHelper.elm` holds a value but no header.

A Standard Definition of Elm?, restriction modules-header: every module begins with a header,
`module M exposing (...)` or `port module M exposing (...)`; a text that does not begin with a
header is not a module of Standard Elm. <https://elm-test-suite.netlify.app/standard/restrictions/modules-header>

-}

-- TAGS: elm-spec, modules-header
-- COMPILE-ERROR: an imported module has no header
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ModuleHeaderMissingHelper


main =
    let
        _ =
            Debug.log "v" ModuleHeaderMissingHelper.v
    in
    Html.text "done"
