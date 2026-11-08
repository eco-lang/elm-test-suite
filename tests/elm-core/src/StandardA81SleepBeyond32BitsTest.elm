module StandardA81SleepBeyond32BitsTest exposing (main)

{-| `Process.sleep d` waits at least `d` milliseconds, also when `d` is above 2^31 - 1.

A Standard Definition of Elm?, ruling A81: the action of `Process.sleep d` takes place no sooner
than `d` milliseconds later, for every finite `d`. <https://elm-test-suite.netlify.app/standard/rules/p-proc-sleep>

A process sleeps for 3e9 ms (about 35 days); 200 ms later it is still asleep, and is killed so that
the program can end. Elm 0.19.1 passes the delay to JavaScript's `setTimeout`, which takes a delay
above 2^31 - 1 as 1 ms: the long sleep ends almost at once. (Killing that finished process then
also stops Elm 0.19.1, elm/core #955.)

-}

-- TAGS: elm19-bug
-- CHECK: checked after 200 ms: ()
-- CHECK-NOT: the long sleep ended

import Process
import Task


type Msg
    = Spawned Process.Id
    | Checked Process.Id
    | Killed


longSleep : Task.Task Never ()
longSleep =
    Process.sleep 3.0e9
        |> Task.andThen
            (\_ ->
                let
                    _ =
                        Debug.log "the long sleep ended" ()
                in
                Task.succeed ()
            )


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Spawned (Process.spawn longSleep) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Spawned pid ->
            ( model, Task.perform (\_ -> Checked pid) (Process.sleep 200) )

        Checked pid ->
            let
                _ =
                    Debug.log "checked after 200 ms" ()
            in
            ( model, Task.perform (\_ -> Killed) (Process.kill pid) )

        Killed ->
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
