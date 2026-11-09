module CharAstralCustomFieldShowTest exposing (main)

{-| `Debug.log` prints a constructor whose field is an astral `Char` (code point above 0xFFFF)
with the character itself: `Box 3 '😀'`.

The code point the field keeps is checked by `CharAstralCustomFieldTest`.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: box_show: Box 3 '😀'

import Html exposing (text)


type Box
    = Box Int Char


main =
    let
        _ =
            Debug.log "box_show" (Box 3 '😀')
    in
    text "done"
