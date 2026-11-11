module StandardA87NumberDefaultCopyTest exposing (main)

{-| A top-level value of type `number` has a Float copy, which is evaluated even when only the Int one is used.

A Standard Definition of Elm?, ruling A87: a program is specialised over its `number` variables
before it runs; a value whose type scheme quantifies one has a default copy at `Float` (ruling A27),
evaluated when its module is, besides a copy for each type it is used at.
<https://elm-test-suite.netlify.app/standard/dynamic-core#sec-dynamic-core-numbers>

`check : number -> number` returns its argument, and logs it unless it is `0`. `x = check (2 ^ -1)`
has the type `number`, and the number variable of `2 ^ -1` is the one in that type, so each copy
of `x` computes `2 ^ -1` at its own type. `x` is used only at `Int`, where `2 ^ -1` is `0` (ruling
A43), so `x // 1` is `0` and the Int copy logs nothing. The default copy, at `Float`, is evaluated
too: there `2 ^ -1` is `0.5`, so it logs. Elm 0.19.1 evaluates `x` once, with its one kind of
number, which behaves as Float, so it logs too. An implementation that makes only the copies a
program uses never logs.

Tagged `elm-unspecced`: the definition evaluates the Float copy of `x`, but an implementation that
makes only the copies a program uses never evaluates it and still conforms on copies (Appendix E,
Number Specialisation), and what `Debug.log` prints is outside the definition (ruling A62). The
first CHECK records what Elm 0.19.1 does.

-}

-- TAGS: elm-unspecced
-- CHECK: the Float copy of x is evaluated: 0.5
-- CHECK: x // 1: 0

import Html


check h =
    if h == 0 then
        h

    else
        Debug.log "the Float copy of x is evaluated" h


x =
    check (2 ^ -1)


main =
    let
        _ =
            Debug.log "x // 1" (x // 1)
    in
    Html.text "done"
