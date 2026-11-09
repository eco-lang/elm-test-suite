module AddTest exposing (main)

{-| `Debug.log` prints an `Int` bound in a `let`.

Despite the module's name, the program does no addition: it logs the literal
42.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: AddTest: 42

import Html exposing (text)


main =
    let
        result =
            42

        _ =
            Debug.log "AddTest" result
    in
    text "hello"
