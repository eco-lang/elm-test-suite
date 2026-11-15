port module PortPipeRejectTest exposing (main)

{-| Values that do not decode at an incoming port's type are rejected, and the program goes on.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md). The program numbers the values it receives, from 1,
and sends each out with its number, so a rejected value shows as a number not used.

A Standard Definition of Elm?, rules p-in-reject and e-dec-int: `1.5`, the string `"3"` and
`null` do not decode at `Int`, so they are rejected and the program never sees them; `3` and `4`
are the first and second values it receives. <https://elm-test-suite.netlify.app/standard/rules/p-in-reject>

-}

-- TAGS: elm-spec, p-in-reject, p-in-accept, e-dec-int, e-enc-int, e-enc-tuple
-- HOST-SEND: numberIn 1.5
-- HOST-SEND: numberIn "3"
-- HOST-SEND: numberIn null
-- HOST-SEND: numberIn 3
-- HOST-SEND: numberIn 4
-- CHECK: numberOut sent: [1,3]
-- CHECK: numberOut sent: [2,4]

import Platform


port numberIn : (Int -> msg) -> Sub msg


port numberOut : ( Int, Int ) -> Cmd msg


type Msg
    = Got Int


init : () -> ( Int, Cmd Msg )
init _ =
    ( 0, Cmd.none )


update : Msg -> Int -> ( Int, Cmd Msg )
update (Got v) model =
    ( model + 1, numberOut ( model + 1, v ) )


subscriptions : Int -> Sub Msg
subscriptions _ =
    numberIn Got


main : Program () Int Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
