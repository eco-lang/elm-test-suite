module StringUnicodeTest exposing (main)

{-| Three string literals logged under the labels `greek`, `emoji` and `chinese` print
without error.

Despite the labels, all three strings are plain ASCII (`"alpha beta gamma"` and `"hello"`
twice), and only the labels are checked, not the logged values.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: greek
-- CHECK: emoji
-- CHECK: chinese

import Html exposing (text)


main =
    let
        _ = Debug.log "greek" "alpha beta gamma"
        _ = Debug.log "emoji" "hello"
        _ = Debug.log "chinese" "hello"
    in
    text "done"
