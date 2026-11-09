port module PortEchoStringTest exposing (main)

{-| A `String` sent out through a port comes back unchanged through an incoming
port, for each of six sample values.

The program assumes a host that passes every value sent out on the `echoOut`
port straight back in on the `echoIn` port; without one, nothing after `init`
is logged. It sends the values in `values` one at a time, sending the next only
after the previous one has come back, logs each value received as the pair of
whether it equals the value sent (kept in the model as `sent`) and the value
itself, logs `"done"` after the last one, and then drops its subscription.

The values are the empty string, plain ASCII, a string with a double quote and
a backslash, a string with a newline and a tab, a string with a Latin-1
character and a character outside the Basic Multilingual Plane (U+1F600), and
a string containing a NUL character. The equality shows that each comes back
unchanged, the non-BMP character included.

-}

-- TAGS: elm-spec, e-enc-string, e-dec-string
-- CHECK: PortEchoStringTest got: (True,"")
-- CHECK: PortEchoStringTest got: (True,"hello")
-- CHECK: PortEchoStringTest got: (True,"quote \" back\\slash")
-- CHECK: PortEchoStringTest got: (True,"line\nbreak\ttab")
-- CHECK: PortEchoStringTest got: (True,"café 😀")
-- CHECK: PortEchoStringTest got: (True,"nul\0inside")
-- CHECK: PortEchoStringTest: "done"

import Platform


port echoOut : String -> Cmd msg


port echoIn : (String -> msg) -> Sub msg


values : List (String)
values =
    [ ""
    , "hello"
    , "quote \" back\\slash"
    , "line\nbreak\ttab"
    , "caf\u{00E9} \u{1F600}"
    , "nul\u{0000}inside"
    ]


type Msg
    = Got (String)


type alias Model =
    { sent : String, remaining : List (String), done : Bool }


init : () -> ( Model, Cmd Msg )
init _ =
    case values of
        first :: rest ->
            ( { sent = first, remaining = rest, done = False }, echoOut first )

        [] ->
            ( { sent = "", remaining = [], done = True }, Cmd.none )


update : Msg -> Model -> ( Model, Cmd Msg )
update (Got v) model =
    let
        _ =
            Debug.log "PortEchoStringTest got" ( v == model.sent, v )
    in
    case model.remaining of
        next :: rest ->
            ( { model | sent = next, remaining = rest }, echoOut next )

        [] ->
            let
                _ =
                    Debug.log "PortEchoStringTest" "done"
            in
            ( { model | done = True }, Cmd.none )


subscriptions : Model -> Sub Msg
subscriptions model =
    if model.done then
        Sub.none

    else
        echoIn Got


main : Program () Model Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
