port module PortPipeMaybeTest exposing (main)

{-| JSON `null` and other values received at `Maybe` types go out as they came.

The test driver sends each `HOST-SEND` value in on the incoming port and prints each value the
program sends out (plans/host-pipe-tests.md); the program passes every value it receives straight
back out. No library function and no `Debug.log` is involved: the driver sees `Enc(Dec(j))`.

A Standard Definition of Elm?, rules e-dec-nothing, e-dec-just, e-enc-nothing and e-enc-just:
`null` decodes as `Nothing`, which is sent as `null`; another value decodes as `Just` of its
value, and a `Just` is sent as its argument. At `Maybe (Maybe Int)`, `null` is the outer
`Nothing`. <https://elm-test-suite.netlify.app/standard/rules/e-dec-just>

-}

-- TAGS: elm-spec, e-dec-nothing, e-dec-just, e-enc-nothing, e-enc-just
-- HOST-SEND: maybeIn [null,null]
-- HOST-SEND: maybeIn [5,7]
-- CHECK: maybeOut sent: [null,null]
-- CHECK: maybeOut sent: [5,7]

import Platform


port maybeIn : (( Maybe Int, Maybe (Maybe Int) ) -> msg) -> Sub msg


port maybeOut : ( Maybe Int, Maybe (Maybe Int) ) -> Cmd msg


type Msg
    = Got ( Maybe Int, Maybe (Maybe Int) )


init : () -> ( (), Cmd Msg )
init _ =
    ( (), Cmd.none )


update : Msg -> () -> ( (), Cmd Msg )
update (Got v) model =
    ( model, maybeOut v )


subscriptions : () -> Sub Msg
subscriptions _ =
    maybeIn Got


main : Program () () Msg
main =
    Platform.worker
        { init = init
        , update = update
        , subscriptions = subscriptions
        }
