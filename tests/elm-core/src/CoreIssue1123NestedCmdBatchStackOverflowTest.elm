module CoreIssue1123NestedCmdBatchStackOverflowTest exposing (main)

{-| A deeply nested `Cmd.batch` overflows the stack in `_Platform_gatherEffects`.

<https://github.com/elm/core/issues/1123>

Elm 0.19.1 recurses once per nesting level and throws `RangeError: Maximum call stack size
exceeded`. The test nests a `Task.perform` inside `Cmd.batch [ acc, Cmd.none ]` 100000 times. That
is a valid command, so the program must run it and receive the inner task's result, 1.

The issue's own program used the library functions `List.foldl` and `List.range` to build the
nesting; this version reproduces the same bug with a local tail-recursive loop in their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, p-init, p-disp-task, e-msg-task, p-proc-message
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
