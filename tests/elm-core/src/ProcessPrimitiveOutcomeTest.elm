module ProcessPrimitiveOutcomeTest exposing (main)

{-| The primitive tasks `Process.sleep`, `Process.spawn` and `Process.kill` succeed with their outcomes.

A Standard Definition of Elm?, rule e-task-prim: a primitive applied to its argument steps to one of
its outcomes, and the task goes on from there. `sleep` and `kill` succeed with `()`, and `spawn`
with the identifier of a process that `kill` then accepts. <https://elm-test-suite.netlify.app/standard/rules/e-task-prim>

-}

-- TAGS: elm-spec, e-task-prim, p-proc-sleep, p-proc-spawn, p-proc-kill, p-wait
-- CHECK: sleep gave: ()
-- CHECK: kill gave: ()

import Process
import Task


type Msg
    = Done ()


sleepThenKill : Task.Task Never ()
sleepThenKill =
    Process.sleep 1
        |> Task.andThen
            (\u ->
                let
                    _ =
                        Debug.log "sleep gave" u
                in
                Process.spawn (Process.sleep 10000)
            )
        |> Task.andThen Process.kill


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Done sleepThenKill )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Done u ->
            let
                _ =
                    Debug.log "kill gave" u
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
