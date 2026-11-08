port module StandardA92BytesPortTest exposing (main)

{-| `Bytes` may cross a port.

A Standard Definition of Elm?, ruling A92: `Bytes` is a payload type, crossing a port as a
sequence of bytes. <https://elm-test-suite.netlify.app/standard/static-modules#sec-static-modules-ports>

The test's host sends each `echoOut` value straight back on `echoIn`. Elm 0.19.1 rejects a port
whose type holds `Bytes`.

-}

-- TAGS: elm19-bug
-- CHECK: received: [1,2,255]

import Bytes exposing (Bytes)
import Bytes.Decode
import Bytes.Encode
import Process
import Task


port echoOut : Bytes -> Cmd msg


port echoIn : (Bytes -> msg) -> Sub msg


type Msg
    = Start
    | Got Bytes


threeBytes : Bytes
threeBytes =
    Bytes.Encode.encode (Bytes.Encode.sequence (List.map Bytes.Encode.unsignedInt8 [ 1, 2, 255 ]))


decodeAll : Bytes -> Maybe (List Int)
decodeAll b =
    Bytes.Decode.decode
        (Bytes.Decode.map3 (\p q r -> [ p, q, r ]) Bytes.Decode.unsignedInt8 Bytes.Decode.unsignedInt8 Bytes.Decode.unsignedInt8)
        b


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Task.perform (always Start) (Process.sleep 10) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Start ->
            ( model, echoOut threeBytes )

        Got b ->
            let
                _ =
                    Debug.log "received" (Maybe.withDefault [] (decodeAll b))
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> echoIn Got
        }
