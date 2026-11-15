module CoreIssue1123NestedCmdBatchStackOverflowTest exposing (main)

{-| A deeply nested `Cmd.batch` overflows the stack in `_Platform_gatherEffects`.

<https://github.com/elm/core/issues/1123>

Elm 0.19.1 recurses once per nesting level and throws `RangeError: Maximum call stack size
exceeded`. The test nests a `Task.perform` inside `Cmd.batch [ acc, Cmd.none ]` 100000 times. That
is a valid command, and by the book the program runs it and receives the inner task's result, 1.

The issue's own program used the library functions `List.foldl` and `List.range` to build the
nesting; this version reproduces the same bug with a local tail-recursive loop in their place.

A Standard Definition of Elm? places no bound on the resources evaluation uses, and an
implementation that stops for lack of them is outside the definition (Appendix,
Implementation-Dependent Details, Resource Limits). The book's result for this program is the one
the test expects, but a compiler that runs out of stack or memory on it does not contradict the
book, so the test is tagged `elm-unspecced`: it checks an implementation's resources.

<https://elm-test-suite.netlify.app/standard/appendix-implementation#sec-appendix-implementation-limits>

-}

-- TAGS: elm19-bug, elm-unspecced
-- CHECK: got: 1

import Task


nest : Int -> Cmd Int -> Cmd Int
nest depth acc =
    if depth <= 0 then
        acc

    else
        nest (depth - 1) (Cmd.batch [ acc, Cmd.none ])


nested : Int -> Cmd Int
nested depth =
    nest depth (Task.perform identity (Task.succeed 1))


main : Program () () Int
main =
    Platform.worker
        { init = \_ -> ( (), nested 100000 )
        , update = \msg model -> ( Debug.log "got" msg |> always model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
