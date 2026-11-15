port module PortPipeScalarsTest exposing (main)

{-| JSON numbers, Booleans, strings and `null` received at `Float`, `Int`, `Bool`, `String`
and `()` go out as they came.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, the Decoding and Encoding rules of the simple types: every JSON
number decodes at `Float`, an integral one at `Int`, and each is sent as the number; `true` and
`false` at `Bool`; a string at `String`; `null` at `()`. The Float `3` is sent as the JSON
number 3. <https://elm-test-suite.netlify.app/standard/rules/e-dec-float>

-}

-- TAGS: elm-spec, e-dec-float, e-enc-float, e-dec-int, e-enc-int, e-dec-true, e-enc-true, e-dec-false, e-enc-false, e-dec-string, e-enc-string, e-dec-unit, e-enc-unit
-- HOST-SEND: scalarsIn {"f":2.5,"i":-3,"s":"x y","t":true,"u":null}
-- HOST-SEND: scalarsIn {"f":3,"i":0,"s":"","t":false,"u":null}
-- CHECK: scalarsOut sent: {"f":2.5,"i":-3,"s":"x y","t":true,"u":null}
-- CHECK: scalarsOut sent: {"f":3,"i":0,"s":"","t":false,"u":null}

import Platform


port scalarsIn : ({ f : Float, i : Int, s : String, t : Bool, u : () } -> msg) -> Sub msg


port scalarsOut : { f : Float, i : Int, s : String, t : Bool, u : () } -> Cmd msg


type Msg
    = Got { f : Float, i : Int, s : String, t : Bool, u : () }


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, scalarsOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    scalarsIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
