port module MinimalPipeTupleTest exposing (main)

{-| A pipe at `( Int, Int )`: the value the driver sends in comes back out.

The simplest test of rules e-dec-tuple, e-enc-tuple of A Standard Definition of Elm?: the driver
sends `[1,2]`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-tuple>

-}

-- TAGS: elm-spec, e-dec-tuple, e-enc-tuple
-- HOST-SEND: pairIn [1,2]
-- CHECK: pairOut sent: [1,2]

import Platform


port pairIn : (( Int, Int ) -> msg) -> Sub msg


port pairOut : ( Int, Int ) -> Cmd msg


type Msg
    = Got ( Int, Int )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, pairOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> pairIn Got
        }
