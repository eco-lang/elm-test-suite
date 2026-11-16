module MinimalTaskPerformTest exposing (main)

{-| The message of a performed task reaches update.

The simplest test of rules e-msg-task, p-disp-task, p-proc-message, p-update of A Standard
Definition of Elm?: init gives `Task.perform Got (Task.succeed 1)`; the task's process ends with its
value, whose message `Got 1` update receives.
<https://elm-test-suite.netlify.app/standard/rules/e-msg-task>

-}

-- TAGS: elm-spec, e-msg-task, p-disp-task, p-proc-message, p-update
-- CHECK: got: 1

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.succeed 1) )


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
