module StandardApplicationStrictTest exposing (main)

{-| A function's argument is evaluated before the function is applied, even when the function does
not use it: `(\_ -> 1) (Debug.todo "x")` has no value, so the program stops there.

A Standard Definition of Elm?, the Comment on rule r:d-exp-app. The program logs `before`, then
stops at `Debug.todo`; `app strict` is never logged, and the program exits with status 1.
<https://elm-test-suite.netlify.app/standard/rules/d-exp-app>

-}

-- TAGS: elm-spec, d-exp-app
-- EXIT: 1
-- CHECK: before: ()
-- CHECK-NOT: app strict:

import Html


main =
    let
        _ =
            Debug.log "before" ()

        _ =
            Debug.log "app strict" ((\_ -> 1) (Debug.todo "x"))
    in
    Html.text "done"
