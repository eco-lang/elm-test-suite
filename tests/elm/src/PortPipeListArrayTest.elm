port module PortPipeListArrayTest exposing (main)

{-| JSON arrays received at `List` and `Array` types go out as the same arrays.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, rules e-dec-list, e-enc-list, e-dec-array and e-enc-array: an
array decodes at `List τ` when each element decodes at `τ`, and at `Array τ` as the array of
that list; both are sent as the array of their elements. No function of the module `Array` is
used. <https://elm-test-suite.netlify.app/standard/rules/e-dec-array>

-}

-- TAGS: elm-spec, e-dec-list, e-enc-list, e-dec-array, e-enc-array, b:Array.Array
-- HOST-SEND: listsIn [[1,2,3],["a","b"]]
-- HOST-SEND: listsIn [[],[]]
-- CHECK: listsOut sent: [[1,2,3],["a","b"]]
-- CHECK: listsOut sent: [[],[]]

import Array exposing (Array)
import Platform


port listsIn : (( List Int, Array String ) -> msg) -> Sub msg


port listsOut : ( List Int, Array String ) -> Cmd msg


type Msg
    = Got ( List Int, Array String )


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, listsOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    listsIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
