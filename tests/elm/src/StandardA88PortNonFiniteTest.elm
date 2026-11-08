port module StandardA88PortNonFiniteTest exposing (main)

{-| A NaN or an infinity sent out through a port arrives as JSON `null`.

A Standard Definition of Elm?, ruling A88: a value crosses a port as JSON, which has no NaN or
infinity, so a non-finite float goes out as `null`. <https://elm-test-suite.netlify.app/standard/rules/e-enc-float>

The test's host sends each `echoOut` value straight back on `echoIn`, decoded as a `Maybe Float`:
`null` is `Nothing`. Elm 0.19.1 passes NaN and `Infinity` to the host as JavaScript numbers, so they
come back as `Just NaN` and `Just Infinity`.

-}

-- TAGS: elm19-bug
-- CHECK: got: Nothing
-- CHECK-NEXT: got: Nothing
-- CHECK-NOT: Just

import Process
import Task


port echoOut : Float -> Cmd msg


port echoIn : (Maybe Float -> msg) -> Sub msg


type Msg
    = Start
    | Got (Maybe Float)


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform (always Start) (Process.sleep 10) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Start ->
            ( model, Cmd.batch (List.map echoOut [ 0 / 0, 1 / 0 ]) )

        Got v ->
            let
                _ =
                    Debug.log "got" (v)
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> echoIn Got
        }
