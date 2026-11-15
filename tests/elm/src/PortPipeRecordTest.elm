port module PortPipeRecordTest exposing (main)

{-| A JSON object received at a record type goes out with exactly the record's fields.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, rules e-dec-record and e-enc-record: an object with further keys
decodes, and they are ignored; a record is sent as the object of its fields, whose order is no
part of what is sent. <https://elm-test-suite.netlify.app/standard/rules/e-dec-record>

-}

-- TAGS: elm-spec, e-dec-record, e-enc-record, e-dec-int, e-enc-int, e-dec-string, e-enc-string
-- HOST-SEND: recordIn {"z":0,"b":{"d":1,"c":"x"},"a":1}
-- CHECK: recordOut sent: {"a":1,"b":{"c":"x"}}

import Platform


port recordIn : ({ a : Int, b : { c : String } } -> msg) -> Sub msg


port recordOut : { a : Int, b : { c : String } } -> Cmd msg


type Msg
    = Got { a : Int, b : { c : String } }


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, recordOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    recordIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
