port module MinimalPipeUnitTest exposing (main)

{-| A pipe at `()`: the value the driver sends in comes back out.

The simplest test of rules e-dec-unit, e-enc-unit of A Standard Definition of Elm?: the driver sends
`null`, the boundary value of `()`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-unit>

-}

-- TAGS: elm-spec, e-dec-unit, e-enc-unit
-- HOST-SEND: unitIn null
-- CHECK: unitOut sent: null

import Platform


port unitIn : (() -> msg) -> Sub msg


port unitOut : () -> Cmd msg


type Msg
    = Got ()


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, unitOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> unitIn Got
        }
