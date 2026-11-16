port module MinimalPipeValueTest exposing (main)

{-| A pipe at `Value`: the value the driver sends in comes back out.

The simplest test of rules e-dec-value, e-enc-value of A Standard Definition of Elm?: the driver
sends `{"a":[1,true]}`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-value>

-}

-- TAGS: elm-spec, e-dec-value, e-enc-value
-- HOST-SEND: valueIn {"a":[1,true]}
-- CHECK: valueOut sent: {"a":[1,true]}

import Json.Encode exposing (Value)
import Platform


port valueIn : (Value -> msg) -> Sub msg


port valueOut : Value -> Cmd msg


type Msg
    = Got Value


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, valueOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> valueIn Got
        }
