port module PortIncomingRejectTest exposing (main)

{-| A value that does not decode at an incoming port's type is rejected, and the program goes on.

A Standard Definition of Elm?, rule p-in-reject: a boundary value that does not decode at the type
of the port is rejected; the program never sees it, and is unchanged. <https://elm-test-suite.netlify.app/standard/rules/p-in-reject>

The program sends `1337` and then `"ok"` out through `echoOut`; the test harness sends each back
in through `echoIn`, whose type is `String`. `1337` must be dropped and `"ok"` received. Elm 0.19.1
throws an exception for `1337` instead (<https://github.com/elm/core/issues/1043>).

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, p-in-reject, p-in-accept
-- CHECK: received: "ok"
-- CHECK-NOT: received: "1337"

import Json.Encode as E


port echoOut : E.Value -> Cmd msg


port echoIn : (String -> msg) -> Sub msg


type Msg
    = Received String


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.batch [ echoOut (E.int 1337), echoOut (E.string "ok") ] )
        , update =
            \(Received s) model ->
                let
                    _ =
                        Debug.log "received" s
                in
                ( model, Cmd.none )
        , subscriptions = \_ -> echoIn Received
        }
