module ImportCycleTest exposing (main)

{-| Modules may not import each other in a cycle.

A Standard Definition of Elm?, restriction program-import-order: each module of a program imports
only modules of the initial basis and modules that stand before it in the program, so there is
no order for `ImportCycleA` and `ImportCycleB`, which import each other.
<https://elm-test-suite.netlify.app/standard/restrictions/program-import-order>

-}

-- TAGS: elm-spec, program-import-order
-- COMPILE-ERROR: two modules that import each other
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ImportCycleA


main =
    let
        _ =
            Debug.log "a" ImportCycleA.a
    in
    Html.text "done"
