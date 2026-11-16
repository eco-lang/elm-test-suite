module MinimalTaskAndThenTest exposing (main)

{-| A task chained after a task that succeeds.

The simplest test of rules e-task-andthen-succeed, p-proc-step of A Standard Definition of Elm?:
`Task.andThen (\_ -> Task.succeed 2) (Task.succeed 1)` steps to the task the function gives.
<https://elm-test-suite.netlify.app/standard/rules/e-task-andthen-succeed>

-}

-- TAGS: elm-spec, e-task-andthen-succeed, p-proc-step
-- CHECK: got: 2

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.andThen (\_ -> Task.succeed 2) (Task.succeed 1)) )


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
