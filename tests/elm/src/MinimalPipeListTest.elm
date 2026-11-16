port module MinimalPipeListTest exposing (main)

{-| A pipe at `List Int`: the value the driver sends in comes back out.

The simplest test of rules e-dec-list, e-enc-list of A Standard Definition of Elm?: the driver sends
`[1,2]`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-list>

-}

-- TAGS: elm-spec, e-dec-list, e-enc-list
-- HOST-SEND: listIn [1,2]
-- CHECK: listOut sent: [1,2]

import Platform


port listIn : (List Int -> msg) -> Sub msg


port listOut : List Int -> Cmd msg


type Msg
    = Got (List Int)


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, listOut v )


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.none )
        , update = update
        , subscriptions = \_ -> listIn Got
        }
