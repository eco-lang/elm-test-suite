module CmdMapComposeTest exposing (main)

{-| `Cmd.map` applies its functions to a command's message, the innermost first.

A Standard Definition of Elm?, rule e-msg-map: the message of `map(v, c)` is `v` applied to the
message of `c`. Of `Cmd.map f (Cmd.map g c)` it is `f (g x)`. <https://elm-test-suite.netlify.app/standard/rules/e-msg-map>

-}

-- TAGS: elm-spec, e-msg-map, e-msg-task
-- CHECK: message: "x then g then f"

import Process
import Task


type Msg
    = Got String


g : String -> String
g s =
    s ++ " then g"


f : String -> Msg
f s =
    Got (s ++ " then f")


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.map f (Cmd.map g (Task.perform identity (Task.succeed "x"))) )


update : Msg -> () -> ( (), Cmd Msg )
update msg model =
    case msg of
        Got s ->
            let
                _ =
                    Debug.log "message" s
            in
            ( model, Cmd.none )


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = \_ -> Sub.none
        }
