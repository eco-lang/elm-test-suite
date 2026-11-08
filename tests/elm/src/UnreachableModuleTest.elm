module UnreachableModuleTest exposing (main)

{-| A module that the main module does not reach is not part of the program, so it does not
matter that it would not compile.

A Standard Definition of Elm?, restriction program-modules-reachable: every module of a program
other than the main module is imported, directly or through other modules, by the main module.
The program is therefore this module and what it imports. `UnreachableBrokenHelper` stands in the
same source directory and has a type error, but nothing imports it, so it is not part of the
program, and the program compiles and runs. A compiler that elaborated every module of the source
directory would reject the program. <https://elm-test-suite.netlify.app/standard/restrictions/program-modules-reachable>

-}

-- TAGS: elm-spec, program-modules-reachable
-- CHECK: ran: True

import Html


main =
    let
        _ =
            Debug.log "ran" True
    in
    Html.text "done"
