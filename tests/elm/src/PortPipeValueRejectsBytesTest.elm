port module PortPipeValueRejectsBytesTest exposing (main)

{-| A byte sequence sent to a `Json.Encode.Value` port is rejected, alone or inside an object.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md). The program numbers the values it receives, from 1,
and sends each out with its number, so a rejected value shows as a number not used.

A Standard Definition of Elm?, rule e-dec-value (ruling A92): every JSON value decodes at
`Value`, and a boundary value in which a byte sequence occurs is not a JSON value, so it does not
decode there and is rejected. `null` after them is the first value the program receives.
<https://elm-test-suite.netlify.app/standard/rules/e-dec-value>

The program's types hold no `Bytes`, so Elm 0.19.1 compiles it, but no compiler the suite runs
has a representation for a byte sequence at the host (Appendix E: Elm/JS has none). To Elm/JS the
driver's `Uint8Array` is a JavaScript value that is not a boundary value, which is outside the
definition, and a `Value` port passes it through; so the test is expected to fail on all of them.

-}

-- TAGS: elm-spec, e-dec-value, e-enc-value, p-in-reject, p-in-accept, e-enc-tuple
-- XFAIL: no compiler the suite runs represents a byte sequence at the host; Elm/JS passes the driver's Uint8Array through a Value port
-- HOST-SEND: valueIn bytes(01)
-- HOST-SEND: valueIn {"a":bytes(02)}
-- HOST-SEND: valueIn null
-- CHECK: valueOut sent: [1,null]

import Json.Encode exposing (Value)
import Platform


port valueIn : (Value -> msg) -> Sub msg


port valueOut : ( Int, Value ) -> Cmd msg


type Msg
    = Got Value


init : () -> ( Int, Cmd Msg )
init _ =
    ( 0, Cmd.none )


update : Msg -> Int -> ( Int, Cmd Msg )
update (Got v) model =
    ( model + 1, valueOut ( model + 1, v ) )


subscriptions : Int -> Sub Msg
subscriptions _ =
    valueIn Got


main : Program () Int Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
