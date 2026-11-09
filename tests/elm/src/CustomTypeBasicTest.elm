module CustomTypeBasicTest exposing (main)

{-| `Debug.log` prints each constructor of a custom type with no arguments by its
name.

The test logs `Red`, `Green` and `Blue` of the type `Color`.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: color1: Red
-- CHECK: color2: Green
-- CHECK: color3: Blue

import Html exposing (text)


type Color
    = Red
    | Green
    | Blue


main =
    let
        _ = Debug.log "color1" Red
        _ = Debug.log "color2" Green
        _ = Debug.log "color3" Blue
    in
    text "done"
