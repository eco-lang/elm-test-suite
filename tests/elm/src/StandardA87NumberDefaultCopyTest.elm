module StandardA87NumberDefaultCopyTest exposing (main)

{-| A top-level value of type `number` has an Int copy, which is evaluated even when only the Float one is used.

A Standard Definition of Elm?, ruling A87: a program is specialised over its `number` variables
before it runs; a value whose type scheme quantifies one has a default copy at `Int`, evaluated when
its module is, besides a copy for each type it is used at.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

`x` is used only at `Float`. At `Int`, `2 ^ -1` is `0`, so its Int copy takes the first branch and
logs; at `Float` it is `0.5`, so `x + 0.5` is `1.5`. Elm 0.19.1 evaluates `x` once, with its one
kind of number, so the first branch never runs.

-}

-- TAGS: elm19-bug
-- CHECK: the Int copy of x is evaluated: 1
-- CHECK: x + 0.5: 1.5

import Html


x =
    if 2 ^ -1 == 0 then
        Debug.log "the Int copy of x is evaluated" 1

    else
        1


main =
    let
        _ =
            Debug.log "x + 0.5" (x + 0.5)
    in
    Html.text "done"
