module BoolTrueFalseTest exposing (main)

{-| The Bool constants `True` and `False` print as `True` and `False` with `Debug.log`.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: true: True
-- CHECK: false: False

import Html exposing (text)


main =
    let
        _ = Debug.log "true" True
        _ = Debug.log "false" False
    in
    text "done"
