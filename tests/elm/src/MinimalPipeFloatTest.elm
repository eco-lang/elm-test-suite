port module MinimalPipeFloatTest exposing (main)

{-| A pipe at `Float`: the value the driver sends in comes back out.

The simplest test of rules e-dec-float, e-enc-float of A Standard Definition of Elm?: the driver
sends `2.5`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-float>

-}

-- TAGS: elm-spec, e-dec-float, e-enc-float
-- HOST-SEND: floatIn 2.5
-- CHECK: floatOut sent: 2.5

import Platform


port floatIn : (Float -> msg) -> Sub msg


port floatOut : Float -> Cmd msg


type Msg
    = Got Float


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, floatOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> floatIn Got
        }
