port module MinimalPipeIntTest exposing (main)

{-| A pipe at `Int`: the value the driver sends in comes back out.

The simplest test of rules e-dec-int, e-enc-int, dm-topdec-port-in, dm-topdec-port-out, p-disp-out,
p-out of A Standard Definition of Elm?: the program declares an incoming and an outgoing port at
`Int`, decodes the `3` the driver sends, and sends it back out, which dispatches it to the port's
queue and then to the host. <https://elm-test-suite.netlify.app/standard/rules/e-dec-int>

-}

-- TAGS: elm-spec, e-dec-int, e-enc-int, dm-topdec-port-in, dm-topdec-port-out, p-disp-out, p-out
-- HOST-SEND: intIn 3
-- CHECK: intOut sent: 3

import Platform


port intIn : (Int -> msg) -> Sub msg


port intOut : Int -> Cmd msg


type Msg
    = Got Int


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, intOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> intIn Got
        }
