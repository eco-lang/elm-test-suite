module ProcessSleepNonFiniteTest exposing (main)

{-| `Process.sleep` given an infinite or NaN delay still wakes, and wakes before a 2000 ms sleep
started at the same time.

Three sleeps are started together from `init`: `1 / 0`, `0 / 0` and 2000 ms. Each of the first
two logs whether it woke before or after the 2000 ms reference. The expected output follows Elm on
node, where `setTimeout` treats a delay outside its supported range as a delay of about 1 ms, so
both are expected to wake first, in any order, and the reference last.

A Standard Definition of Elm? does not decide this test: when the action of a sleep whose delay is
an infinity or NaN takes place is not defined (ruling A81). A finite delay, however large, is
waited for in full; `StandardA81SleepBeyond32BitsTest` checks that.
<https://elm-test-suite.netlify.app/standard/rules/p-proc-sleep>

-}

-- TAGS: elm-unspecced
-- CHECK-DAG: sleep: "inf: woke first"
-- CHECK-DAG: sleep: "nan: woke first"
-- CHECK: sleep: "reference woke"

import Platform
import Process
import Task


type Msg
    = Woke String
    | Reference


type alias Model =
    { referenceDone : Bool }


init : () -> ( Model, Cmd Msg )
init _ =
    ( { referenceDone = False }
    , Cmd.batch
        [ Task.perform (\_ -> Woke "inf") (Process.sleep (1 / 0))
        , Task.perform (\_ -> Woke "nan") (Process.sleep (0 / 0))
        , Task.perform (\_ -> Reference) (Process.sleep 2000)
        ]
    )


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        Woke name ->
            let
                _ =
                    if model.referenceDone then
                        Debug.log "sleep" (name ++ ": woke after the reference")

                    else
                        Debug.log "sleep" (name ++ ": woke first")
            in
            ( model, Cmd.none )

        Reference ->
            let
                _ =
                    Debug.log "sleep" "reference woke"
            in
            ( { model | referenceDone = True }, Cmd.none )


main : Program () Model Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
