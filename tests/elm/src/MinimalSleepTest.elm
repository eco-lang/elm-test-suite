module MinimalSleepTest exposing (main)

{-| A process sleeps, and time passes.

The simplest test of rules e-task-prim, p-proc-sleep, p-wait of A Standard Definition of Elm?:
`Process.sleep 10` is a primitive of the platform; the process takes its step once 10 milliseconds
have passed, and its task succeeds with `()`.
<https://elm-test-suite.netlify.app/standard/rules/e-task-prim>

-}

-- TAGS: elm-spec, e-task-prim, p-proc-sleep, p-wait
-- CHECK: got: ()

import Process
import Task


type Msg
    = Got ()


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Process.sleep 10) )


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
