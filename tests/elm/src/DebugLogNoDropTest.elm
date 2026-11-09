module DebugLogNoDropTest exposing (main)

{-| A `Debug.log` call inside an unused `let` binding still prints.

`deadLogged` is never read; its value is `String.length` applied to
`Debug.log "kept" "logged"`, and the test checks that the line
`kept: "logged"` is printed. The second unused binding, `deadPure`, contains no
`Debug` call and has no observable effect.

The relative order of the logged lines is not checked.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: kept: "logged"

import Html exposing (text)


main : Html.Html msg
main =
    let
        deadLogged =
            String.length (Debug.log "kept" "logged")

        deadPure =
            String.length "xyz"
    in
    text "done"
