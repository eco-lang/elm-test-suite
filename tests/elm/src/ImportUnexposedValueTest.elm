module ImportUnexposedValueTest exposing (main)

{-| A value its module's header does not expose cannot be used, even qualified.

A Standard Definition of Elm?, rule sm-header: a module's interface is what its header exposes.
`ModuleExposingHelper` declares `hidden` but does not expose it. <https://elm-test-suite.netlify.app/standard/rules/sm-header>

-}

-- TAGS: elm-spec, sm-header
-- COMPILE-ERROR: a use of a value the imported module does not expose
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ModuleExposingHelper


main =
    let
        _ =
            Debug.log "hidden" ModuleExposingHelper.hidden
    in
    Html.text "done"
