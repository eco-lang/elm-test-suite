port module PortPipeBytesRejectTest exposing (main)

{-| A JSON value sent to a `Bytes` port is rejected, whatever it holds.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md). The program numbers the values it receives, from 1,
and sends each out with its number, so a rejected value shows as a number not used.

A Standard Definition of Elm?, rules e-dec-bytes and p-in-reject (rulings A71, A92): only a byte
sequence decodes at `Bytes`; a string of hex digits, an array of numbers and `null` are JSON
values, and are rejected at the boundary. The byte sequence after them is the first value the
program receives. <https://elm-test-suite.netlify.app/standard/rules/e-dec-bytes>

Elm 0.19.1 rejects every port whose type holds `Bytes` (PORT ERROR); Appendix E of the book says
Elm/JS has no representation for a byte sequence at the host.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, e-dec-bytes, e-enc-bytes, p-in-reject, p-in-accept, e-enc-tuple, b:Bytes.Bytes
-- HOST-SEND: bytesIn "00ff10"
-- HOST-SEND: bytesIn [0,255,16]
-- HOST-SEND: bytesIn null
-- HOST-SEND: bytesIn bytes(01)
-- CHECK: bytesOut sent: [1,bytes(01)]

import Bytes exposing (Bytes)
import Platform


port bytesIn : (Bytes -> msg) -> Sub msg


port bytesOut : ( Int, Bytes ) -> Cmd msg


type Msg
    = Got Bytes


init : () -> ( Int, Cmd Msg )
init _ =
    ( 0, Cmd.none )


update : Msg -> Int -> ( Int, Cmd Msg )
update (Got v) model =
    ( model + 1, bytesOut ( model + 1, v ) )


subscriptions : Int -> Sub Msg
subscriptions _ =
    bytesIn Got


main : Program () Int Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
