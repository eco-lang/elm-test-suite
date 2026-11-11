module StandardA93MutualNumberDefaultTest exposing (main)

{-| A `number` variable of a recursive group that one binding's type does not mention is Float at a
use of that binding.

`f` and `g` call each other, so they are one group. `g : b -> number -> b`, with `b` of class
`number`; `f`'s type does not mention `b`, but `f`'s body uses `g` at `b`. A Standard Definition of
Elm?, ruling A93: closing the group closes `f`'s scheme over `b` too, so the use `f 3` gives `b` a
type that nothing fixes, which number specialisation makes Float (ruling A27). Then `g 1 2` is `2`,
`2 ^ -1` is `0.5` and `f 3` is `1`. <https://elm-test-suite.netlify.app/standard/static-core#sec-static-core-closure>

Elm 0.19.1 has one representation for Int and Float on JavaScript, so it gives the same answer. An
implementation that makes `b` Int has `2 ^ -1` as `0` (ruling A43) and `f 3` as `0`.

-}

-- TAGS: elm-spec, s-dec-group, sec:static-core-closure, sec:dynamic-core-numbers
-- CHECK: f 3: 1

import Html exposing (text)


f n =
    if n <= 0 then
        0

    else if g 1 (n - 1) ^ -1 > 0 then
        1

    else
        0


g y k =
    if k <= 0 then
        y + 1

    else
        let
            _ =
                f k
        in
        y + 1


main =
    let
        _ =
            Debug.log "f 3" (f 3)
    in
    text "done"
