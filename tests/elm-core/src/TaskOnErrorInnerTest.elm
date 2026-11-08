module TaskOnErrorInnerTest exposing (main)

{-| `Task.onError` lets its task take steps before it succeeds or fails.

A Standard Definition of Elm?, rule e-task-onerror-inner: the task inside `onError` reduces step by
step, here through a sleep and an `andThen`, before rule e-task-onerror-fail hands its error to
the handler or rule e-task-onerror-succeed passes its value through. <https://elm-test-suite.netlify.app/standard/rules/e-task-onerror-inner>

-}

-- TAGS: elm-spec, e-task-onerror-inner, e-task-onerror-fail, e-task-onerror-succeed, e-task-andthen-inner
-- CHECK: failed then handled: 70
-- CHECK: succeeded through: 5

import Process
import Task


type Msg
    = Failed Int
    | Succeeded Int


failsLater : Task.Task Int Int
failsLater =
    Process.sleep 1 |> Task.andThen (\_ -> Task.fail 7)


succeedsLater : Task.Task Int Int
succeedsLater =
    Process.sleep 1 |> Task.andThen (\_ -> Task.succeed 5)


handled : Task.Task Int Int -> Task.Task Never Int
handled task =
    task |> Task.onError (\e -> Task.succeed (e * 10))


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.batch [ Task.perform Failed (handled failsLater), Task.perform Succeeded (handled succeedsLater) ] )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Failed n ->
            let
                _ =
                    Debug.log "failed then handled" n
            in
            ( model, Cmd.none )

        Succeeded n ->
            let
                _ =
                    Debug.log "succeeded through" n
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
