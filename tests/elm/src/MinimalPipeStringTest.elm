port module MinimalPipeStringTest exposing (main)

{-| A pipe at `String`: the value the driver sends in comes back out.

The simplest test of rules e-dec-string, e-enc-string of A Standard Definition of Elm?: the driver
sends `"a"`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-string>

-}

-- TAGS: elm-spec, e-dec-string, e-enc-string
-- HOST-SEND: stringIn "a"
-- CHECK: stringOut sent: "a"

import Platform


port stringIn : (String -> msg) -> Sub msg


port stringOut : String -> Cmd msg


type Msg
    = Got String


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, stringOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> stringIn Got
        }
