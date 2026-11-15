port module PortPipeValueTest exposing (main)

{-| A JSON value received at `Json.Encode.Value` goes out again as the same JSON value.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, rules e-dec-value and e-enc-value: every JSON value decodes at
`Value` as itself, and a `Value` is sent as the JSON value it is. Objects have no order, so the
driver prints keys in increasing order; the array `[1,true,null]`, which no other Elm type decodes,
passes through unchanged. <https://elm-test-suite.netlify.app/standard/rules/e-dec-value>

-}

-- TAGS: elm-spec, e-dec-value, e-enc-value, p-in-accept, p-out
-- HOST-SEND: valueIn {"b":[1,true,null],"a":"x","c":{}}
-- HOST-SEND: valueIn "plain"
-- HOST-SEND: valueIn -2.5
-- HOST-SEND: valueIn null
-- HOST-SEND: valueIn [[],{"k":[{}]}]
-- CHECK: valueOut sent: {"a":"x","b":[1,true,null],"c":{}}
-- CHECK: valueOut sent: "plain"
-- CHECK: valueOut sent: -2.5
-- CHECK: valueOut sent: null
-- CHECK: valueOut sent: [[],{"k":[{}]}]

import Json.Encode exposing (Value)
import Platform


port valueIn : (Value -> msg) -> Sub msg


port valueOut : Value -> Cmd msg


type Msg
    = Got Value


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, valueOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    valueIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
