module ImportedModuleTypeErrorTest exposing (main)

{-| A program whose imported module has a type error is rejected as a whole.

A Standard Definition of Elm?, rule p-program: a program is elaborated as a whole before any part
of it is evaluated, so when one module fails to elaborate nothing is evaluated.
`ImportedModuleTypeErrorHelper` adds a String to an Int. <https://elm-test-suite.netlify.app/standard/rules/p-program>

-}

-- TAGS: elm-spec, p-program
-- COMPILE-ERROR: a type error in an imported module
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ImportedModuleTypeErrorHelper


main =
    let
        _ =
            Debug.log "ran" True

        _ =
            Debug.log "value" ImportedModuleTypeErrorHelper.value
    in
    Html.text "done"
