port module MinimalPortSubscriptionTest exposing (main)

{-| A value sent in on a port reaches update as the subscription's message.

The simplest test of rule e-msg-port of A Standard Definition of Elm?: the driver sends `5` on
`numIn`, to which the program subscribes with `Got`.
<https://elm-test-suite.netlify.app/standard/rules/e-msg-port>

-}

-- TAGS: elm-spec, e-msg-port
-- HOST-SEND: numIn 5
-- CHECK: got: 5

import Platform


port numIn : (Int -> msg) -> Sub msg


type Msg
    = Got Int


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    let
        _ =
            Debug.log "got" v
    in
    ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> numIn Got
        }
