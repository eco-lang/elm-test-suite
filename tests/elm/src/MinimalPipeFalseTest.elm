port module MinimalPipeFalseTest exposing (main)

{-| A pipe at `Bool`: the value the driver sends in comes back out.

The simplest test of rules e-dec-false, e-enc-false of A Standard Definition of Elm?: the driver
sends `false`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-false>

-}

-- TAGS: elm-spec, e-dec-false, e-enc-false
-- HOST-SEND: boolIn false
-- CHECK: boolOut sent: false

import Platform


port boolIn : (Bool -> msg) -> Sub msg


port boolOut : Bool -> Cmd msg


type Msg
    = Got Bool


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, boolOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> boolIn Got
        }
