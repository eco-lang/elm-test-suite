port module StandardA88PortNegativeZeroTest exposing (main)

{-| `-0` sent out through a port arrives as `+0`.

A Standard Definition of Elm?, ruling A88: a value crosses a port as JSON, where `-0` is the number
`0`; at `Float` it decodes as `+0`. <https://elm-test-suite.netlify.app/standard/rules/e-enc-float>
<https://elm-test-suite.netlify.app/standard/rules/e-dec-float>

The test's host sends each `echoOut` value straight back on `echoIn`. Elm 0.19.1 passes `-0`
through, so `1 / v` is `-Infinity`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, e-enc-float, e-dec-float
-- CHECK: 1 / received > 0: True

import Process
import Task


port echoOut : Float -> Cmd msg


port echoIn : (Float -> msg) -> Sub msg


type Msg
    = Start
    | Got Float


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform (always Start) (Process.sleep 10) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Start ->
            ( model, Cmd.batch (List.map echoOut [ -(0 / 1) ]) )

        Got v ->
            let
                _ =
                    Debug.log "1 / received > 0" (1 / v > 0)
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> echoIn Got
        }
