port module MinimalPipeNothingTest exposing (main)

{-| A pipe at `Maybe Int`: the value the driver sends in comes back out.

The simplest test of rules e-dec-nothing, e-enc-nothing of A Standard Definition of Elm?: the driver
sends `null`, which is `Nothing`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-nothing>

-}

-- TAGS: elm-spec, e-dec-nothing, e-enc-nothing
-- HOST-SEND: maybeIn null
-- CHECK: maybeOut sent: null

import Platform


port maybeIn : (Maybe Int -> msg) -> Sub msg


port maybeOut : Maybe Int -> Cmd msg


type Msg
    = Got (Maybe Int)


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, maybeOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> maybeIn Got
        }
