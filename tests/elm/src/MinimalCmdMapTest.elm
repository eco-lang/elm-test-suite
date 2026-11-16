module MinimalCmdMapTest exposing (main)

{-| A command mapped by a function gives the mapped message.

The simplest test of rule e-msg-map of A Standard Definition of Elm?: `Cmd.map Got (Task.perform
identity (Task.succeed 1))`. <https://elm-test-suite.netlify.app/standard/rules/e-msg-map>

-}

-- TAGS: elm-spec, e-msg-map
-- CHECK: got: 1

import Task


type Msg
    = Got Int


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.map Got (Task.perform identity (Task.succeed 1)) )


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
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
