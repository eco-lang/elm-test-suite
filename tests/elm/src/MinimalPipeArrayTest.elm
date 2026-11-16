port module MinimalPipeArrayTest exposing (main)

{-| A pipe at `Array Int`: the value the driver sends in comes back out.

The simplest test of rules e-dec-array, e-enc-array of A Standard Definition of Elm?: the driver
sends `[1,2]`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-array>

-}

-- TAGS: elm-spec, e-dec-array, e-enc-array
-- HOST-SEND: arrayIn [1,2]
-- CHECK: arrayOut sent: [1,2]

import Array exposing (Array)
import Platform


port arrayIn : (Array Int -> msg) -> Sub msg


port arrayOut : Array Int -> Cmd msg


type Msg
    = Got (Array Int)


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, arrayOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> arrayIn Got
        }
