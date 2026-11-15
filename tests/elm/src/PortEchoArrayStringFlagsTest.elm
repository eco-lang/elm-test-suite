port module PortEchoArrayStringFlagsTest exposing (main)

{-| An `Array String` sent out through a port comes back unchanged through an incoming
port, for each of two sample values received as flags.

The program assumes a host that passes every value sent out on the `echoOut`
port straight back in on the `echoIn` port; without one, nothing after `init`
is logged. It sends the values one at a time, sending the next only after the
previous one has come back, logs each value received, logs `"done"` after the
last one, and then drops its subscription.

The values are an empty array and a three-element array. They arrive as the
flags, a JSON array of arrays decoded at `List (Array String)`, because within A
Standard Definition of Elm? an array reaches a program only through its flags or
a port: the functions of `Array` that build one are library, outside the
definition. `PortEchoArrayStringTest` checks the same round trip with arrays the
program builds itself.

-}

-- TAGS: elm-spec, e-enc-array, e-dec-array, e-enc-string, e-dec-string, b:Array.Array
-- FLAGS: [[],["a","b","c"]]
-- CHECK: PortEchoArrayStringFlagsTest got: Array.fromList []
-- CHECK: PortEchoArrayStringFlagsTest got: Array.fromList ["a","b","c"]
-- CHECK: PortEchoArrayStringFlagsTest: "done"

import Array exposing (Array)
import Platform


port echoOut : Array String -> Cmd msg


port echoIn : (Array String -> msg) -> Sub msg


type Msg
    = Got (Array String)


type alias Model =
    { remaining : List (Array String), done : Bool }


init : List (Array String) -> ( Model, Cmd Msg )
init values =
    case values of
        first :: rest ->
            ( { remaining = rest, done = False }, echoOut first )

        [] ->
            ( { remaining = [], done = True }, Cmd.none )


update : Msg -> Model -> ( Model, Cmd Msg )
update (Got v) model =
    let
        _ =
            Debug.log "PortEchoArrayStringFlagsTest got" v
    in
    case model.remaining of
        next :: rest ->
            ( { model | remaining = rest }, echoOut next )

        [] ->
            let
                _ =
                    Debug.log "PortEchoArrayStringFlagsTest" "done"
            in
            ( { model | done = True }, Cmd.none )


subscriptions : Model -> Sub Msg
subscriptions model =
    if model.done then
        Sub.none

    else
        echoIn Got


main : Program (List (Array String)) Model Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
