module ProcessSpawnedFailureEndsTest exposing (main)

{-| A spawned process whose task fails ends quietly, and the program goes on.

A Standard Definition of Elm?, rule p-proc-end: a process whose task fails ends, whatever its
origin, and nothing else happens: there is no error and no message. The program spawns a task
that fails at once, then sleeps 20 ms and logs that it is still running. <https://elm-test-suite.netlify.app/standard/rules/p-proc-end>

-}

-- TAGS: elm-spec, p-proc-end, p-proc-spawn
-- CHECK: spawned: True
-- CHECK: still running: True

import Process
import Task


type Msg
    = Spawned
    | Later


failing : Task.Task String ()
failing =
    Task.fail "boom"


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform (\_ -> Spawned) (Process.spawn failing) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Spawned ->
            let
                _ =
                    Debug.log "spawned" True
            in
            ( model, Task.perform (\_ -> Later) (Process.sleep 20) )

        Later ->
            let
                _ =
                    Debug.log "still running" True
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
