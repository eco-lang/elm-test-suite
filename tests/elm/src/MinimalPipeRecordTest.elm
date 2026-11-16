port module MinimalPipeRecordTest exposing (main)

{-| A pipe at `{ a : Int }`: the value the driver sends in comes back out.

The simplest test of rules e-dec-record, e-enc-record of A Standard Definition of Elm?: the driver
sends `{"a":1}`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-record>

-}

-- TAGS: elm-spec, e-dec-record, e-enc-record
-- HOST-SEND: recordIn {"a":1}
-- CHECK: recordOut sent: {"a":1}

import Platform


port recordIn : ({ a : Int } -> msg) -> Sub msg


port recordOut : { a : Int } -> Cmd msg


type Msg
    = Got { a : Int }


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, recordOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> recordIn Got
        }
