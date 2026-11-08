module StandardA82MainInImportedModuleTest exposing (main)

{-| A `main` in a module other than the main module is an ordinary value, of any type.

A Standard Definition of Elm?, rulings A32 and A82: only the `main` of the main module must have a
program type; a `main` in any other module is an ordinary value.
<https://elm-test-suite.netlify.app/standard/rules/p-stat-main-program>

`StandardA82MainHelper.main` is `42`, an `Int`. Elm 0.19.1 rejects the helper module because its
`main` is not a program.

-}

-- TAGS: elm19-bug
-- CHECK: helper main + 1: 43

import Html
import StandardA82MainHelper


main =
    let
        _ =
            Debug.log "helper main + 1" (StandardA82MainHelper.main + 1)
    in
    Html.text "done"
