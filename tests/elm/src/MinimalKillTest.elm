module MinimalKillTest exposing (main)

{-| A process kills a process it spawned.

The simplest test of rule p-proc-kill of A Standard Definition of Elm?: a process spawns one that
sleeps, kills it with `Process.kill`, and gives `3`.
<https://elm-test-suite.netlify.app/standard/rules/p-proc-kill>

-}

-- TAGS: elm-spec, p-proc-kill
-- CHECK: got: 3

import Process
import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.andThen (\_ -> Task.succeed 3) (Task.andThen Process.kill (Process.spawn (Process.sleep 1000)))) )


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
