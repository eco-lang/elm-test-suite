port module PortEchoJsonValueTest exposing (main)

{-| JSON `Value`s received as flags are sent out through a port as they are, and come back
through an incoming port decoded at a concrete type.

The program assumes a host that passes every value sent out on the `echoOut` port straight back
in on the `echoIn` port; without one, nothing after `init` is logged.

The flags are a JSON object whose four fields are decoded at `Json.Encode.Value`: an object
holding an array and a string, a JSON string, a JSON number (2.5), and `null`. Every JSON value
decodes at `Value`, unchanged. `init` sends the four out together, as a triple whose last
component is a pair, and a `Value` is sent as the JSON value it is, so the host receives
`[{"a":[1,2,null],"b":"x"},"plain",[2.5,null]]`. That comes back on `echoIn`, decoded at a
type that reads every part: a record, a string, and a pair of a `Float` and a `Maybe Int`. The
program logs it and drops its subscription.

A Standard Definition of Elm? gives `Value` no functions within the definition, and does not fix
what `Debug.log` prints for one, so the Values are observed through the type they decode at.

-}

-- TAGS: elm-spec, e-enc-value, e-dec-value
-- FLAGS: {"obj":{"a":[1,2,null],"b":"x"},"str":"plain","num":2.5,"nul":null}
-- CHECK: PortEchoJsonValueTest got: ({ a = [Just 1,Just 2,Nothing], b = "x" },"plain",(2.5,Nothing))

import Json.Encode exposing (Value)
import Platform


port echoOut : ( Value, Value, ( Value, Value ) ) -> Cmd msg


port echoIn : (( { a : List (Maybe Int), b : String }, String, ( Float, Maybe Int ) ) -> msg) -> Sub msg


type alias Flags =
    { obj : Value, str : Value, num : Value, nul : Value }


type Msg
    = Got ( { a : List (Maybe Int), b : String }, String, ( Float, Maybe Int ) )


init : Flags -> ( Bool, Cmd Msg )
init flags =
    ( False, echoOut ( flags.obj, flags.str, ( flags.num, flags.nul ) ) )


update : Msg -> Bool -> ( Bool, Cmd Msg )
update (Got v) _ =
    let
        _ =
            Debug.log "PortEchoJsonValueTest got" v
    in
    ( True, Cmd.none )


subscriptions : Bool -> Sub Msg
subscriptions done =
    if done then
        Sub.none

    else
        echoIn Got


main : Program Flags Bool Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
