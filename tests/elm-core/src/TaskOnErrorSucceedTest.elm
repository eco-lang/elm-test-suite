module TaskOnErrorSucceedTest exposing (main)

{-| `Task.onError` on a task that succeeds gives that task's value; the handler is not called.

A Standard Definition of Elm?, rule e-task-onerror-succeed: `onError(v, succeed v')` reduces to
`succeed v'`. <https://elm-test-suite.netlify.app/standard/rules/e-task-onerror-succeed>

-}

-- TAGS: elm-spec, e-task-onerror-succeed
-- CHECK: result: 1
-- CHECK-NOT: handler called

import Process
import Task


type Msg
    = Got Int


handler : x -> Task.Task Never Int
handler _ =
    let
        _ =
            Debug.log "handler called" ()
    in
    Task.succeed 2


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform Got (Task.succeed 1 |> Task.onError handler) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Got n ->
            let
                _ =
                    Debug.log "result" n
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
