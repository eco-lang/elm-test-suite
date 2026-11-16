module MinimalTaskAndThenInnerTest exposing (main)

{-| A chained task whose first task takes steps of its own.

The simplest test of rule e-task-andthen-inner of A Standard Definition of Elm?: the first task of
the outer `Task.andThen` is itself a `Task.andThen`, which reduces inside it before the outer
function is applied. <https://elm-test-suite.netlify.app/standard/rules/e-task-andthen-inner>

-}

-- TAGS: elm-spec, e-task-andthen-inner
-- CHECK: got: 2

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.andThen (\_ -> Task.succeed 2) (Task.andThen (\_ -> Task.succeed 1) (Task.succeed 0))) )


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
