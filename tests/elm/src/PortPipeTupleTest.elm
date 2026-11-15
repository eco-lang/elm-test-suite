port module PortPipeTupleTest exposing (main)

{-| A JSON array received at a tuple type goes out with as many elements as the tuple has.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, rules e-dec-tuple and e-enc-tuple: an array at least as long as
the tuple decodes, and its further elements are ignored; a tuple is sent as the array of its
components. Here a 3-tuple holds a 2-tuple. <https://elm-test-suite.netlify.app/standard/rules/e-dec-tuple>

-}

-- TAGS: elm-spec, e-dec-tuple, e-enc-tuple, e-dec-int, e-enc-int, e-dec-string, e-enc-string, e-dec-false, e-enc-false
-- HOST-SEND: tupleIn [1,["a",false,"extra"],7]
-- HOST-SEND: tupleIn [2,["b",false],8,null,"more"]
-- CHECK: tupleOut sent: [1,["a",false],7]
-- CHECK: tupleOut sent: [2,["b",false],8]

import Platform


port tupleIn : (( Int, ( String, Bool ), Int ) -> msg) -> Sub msg


port tupleOut : ( Int, ( String, Bool ), Int ) -> Cmd msg


type Msg
    = Got ( Int, ( String, Bool ), Int )


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, tupleOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    tupleIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
