port module MinimalPipeTrueTest exposing (main)

{-| A pipe at `Bool`: the value the driver sends in comes back out.

The simplest test of rules e-dec-true, e-enc-true of A Standard Definition of Elm?: the driver sends
`true`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-true>

-}

-- TAGS: elm-spec, e-dec-true, e-enc-true
-- HOST-SEND: boolIn true
-- CHECK: boolOut sent: true

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
