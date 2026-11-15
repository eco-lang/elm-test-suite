port module PortPipeBytesTest exposing (main)

{-| A byte sequence received at `Bytes` goes out again as the same byte sequence.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No function of elm/bytes is used: within the book's basis a program can have a `Bytes`
value only from the boundary.

A Standard Definition of Elm?, rules e-dec-bytes and e-enc-bytes (ruling A92): a byte sequence
decodes at `Bytes` as the value of its bytes, and a `Bytes` value is sent as its byte sequence.
The empty sequence is a byte sequence too. <https://elm-test-suite.netlify.app/standard/rules/e-dec-bytes>

Elm 0.19.1 rejects every port whose type holds `Bytes` (PORT ERROR); Appendix E of the book says
Elm/JS has no representation for a byte sequence at the host.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, e-dec-bytes, e-enc-bytes, p-in-accept, p-out, b:Bytes.Bytes
-- HOST-SEND: bytesIn bytes(00 ff 10)
-- HOST-SEND: bytesIn bytes()
-- CHECK: bytesOut sent: bytes(00 ff 10)
-- CHECK: bytesOut sent: bytes()

import Bytes exposing (Bytes)
import Platform


port bytesIn : (Bytes -> msg) -> Sub msg


port bytesOut : Bytes -> Cmd msg


type Msg
    = Got Bytes


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, bytesOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    bytesIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
