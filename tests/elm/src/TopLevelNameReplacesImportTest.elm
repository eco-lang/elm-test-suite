module TopLevelNameReplacesImportTest exposing (main)

{-| A name a module declares replaces, within it, an imported name spelt alike.

A Standard Definition of Elm?, rule dm-module: the top-level declarations are evaluated in the
environment the imports give, modified by the module's own, so this module's `max` (which adds)
replaces `Basics.max`, which stays reachable qualified. <https://elm-test-suite.netlify.app/standard/rules/dm-module>

-}

-- TAGS: elm-spec, dm-module
-- CHECK: own max: 3
-- CHECK: Basics.max: 2

import Html


max : Int -> Int -> Int
max x y =
    x + y


main =
    let
        _ =
            Debug.log "own max" (max 1 2)

        _ =
            Debug.log "Basics.max" (Basics.max 1 2)
    in
    Html.text "done"
