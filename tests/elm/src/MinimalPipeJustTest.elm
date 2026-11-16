port module MinimalPipeJustTest exposing (main)

{-| A pipe at `Maybe Int`: the value the driver sends in comes back out.

The simplest test of rules e-dec-just, e-enc-just of A Standard Definition of Elm?: the driver sends
`5`, which is `Just 5`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-just>

-}

-- TAGS: elm-spec, e-dec-just, e-enc-just
-- HOST-SEND: maybeIn 5
-- CHECK: maybeOut sent: 5

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
