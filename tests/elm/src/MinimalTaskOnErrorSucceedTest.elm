module MinimalTaskOnErrorSucceedTest exposing (main)

{-| An error handler is not used when the task succeeds.

The simplest test of rule e-task-onerror-succeed of A Standard Definition of Elm?: `Task.onError (\_
-> Task.succeed 2) (Task.succeed 1)` succeeds with `1`.
<https://elm-test-suite.netlify.app/standard/rules/e-task-onerror-succeed>

-}

-- TAGS: elm-spec, e-task-onerror-succeed
-- CHECK: got: 1

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.onError (\_ -> Task.succeed 2) (Task.succeed 1)) )


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
