module MinimalTaskOnErrorInnerTest exposing (main)

{-| A handled task whose task takes steps of its own.

The simplest test of rule e-task-onerror-inner of A Standard Definition of Elm?: the task of
`Task.onError` is a `Task.andThen` on a failing task, which reduces to the failure inside it; the
handler then gives `3`. <https://elm-test-suite.netlify.app/standard/rules/e-task-onerror-inner>

-}

-- TAGS: elm-spec, e-task-onerror-inner
-- CHECK: got: 3

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.onError (\_ -> Task.succeed 3) (Task.andThen (\_ -> Task.succeed 1) (Task.fail 0))) )


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
