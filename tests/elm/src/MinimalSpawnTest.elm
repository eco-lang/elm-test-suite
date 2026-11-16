module MinimalSpawnTest exposing (main)

{-| A spawned process runs, and ends when its task succeeds.

The simplest test of rules p-proc-spawn, p-proc-end of A Standard Definition of Elm?: `Process.spawn
(Task.succeed 1)` starts a process, which ends; the spawning task then gives `2`.
<https://elm-test-suite.netlify.app/standard/rules/p-proc-spawn>

-}

-- TAGS: elm-spec, p-proc-spawn, p-proc-end
-- CHECK: got: 2

import Process
import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.andThen (\_ -> Task.succeed 2) (Process.spawn (Task.succeed 1))) )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    let
        _ =
            Debug.log "got" v
    in
    ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
