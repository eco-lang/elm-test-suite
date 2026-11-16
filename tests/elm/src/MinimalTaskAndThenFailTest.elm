module MinimalTaskAndThenFailTest exposing (main)

{-| A task chained after a task that fails fails with the same error.

The simplest test of rule e-task-andthen-fail of A Standard Definition of Elm?: `Task.andThen (\_ ->
Task.succeed 2) (Task.fail 1)` fails with `1`, which `Task.attempt` gives as `Err 1`.
<https://elm-test-suite.netlify.app/standard/rules/e-task-andthen-fail>

-}

-- TAGS: elm-spec, e-task-andthen-fail
-- CHECK: got: Err 1

import Task


type Msg
    = Got (Result Int Int)


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.attempt Got (Task.andThen (\_ -> Task.succeed 2) (Task.fail 1)) )


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
