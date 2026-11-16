module MinimalTaskOnErrorTest exposing (main)

{-| An error handler replaces a task that fails.

The simplest test of rule e-task-onerror-fail of A Standard Definition of Elm?: `Task.onError (\_ ->
Task.succeed 2) (Task.fail 1)` steps to the handler's task.
<https://elm-test-suite.netlify.app/standard/rules/e-task-onerror-fail>

-}

-- TAGS: elm-spec, e-task-onerror-fail
-- CHECK: got: 2

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.onError (\_ -> Task.succeed 2) (Task.fail 1)) )


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
