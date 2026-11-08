module LetValueBindingTest exposing (main)

{-| A `let` binding `x = e` binds `x` to the value of `e`, evaluated once.

A Standard Definition of Elm?, rule d-valbind-var: the value binding `x = e` evaluates `e` and
binds `x` to its value. The bound value is used twice; the `Debug.log` in `e` shows it is
evaluated once. <https://elm-test-suite.netlify.app/standard/rules/d-valbind-var>

-}

-- TAGS: elm-spec, d-valbind-var, d-atexp-let
-- CHECK: evaluated: 21
-- CHECK: doubled: 42

import Html


main =
    let
        x =
            Debug.log "evaluated" (20 + 1)

        _ =
            Debug.log "doubled" (x + x)
    in
    Html.text "done"
