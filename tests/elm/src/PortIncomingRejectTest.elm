port module PortIncomingRejectTest exposing (main)

{-| A value that does not decode at an incoming port's type is rejected, and the program goes on.

A Standard Definition of Elm?, rule p-in-reject: a boundary value that does not decode at the type
of the port is rejected; the program never sees it, and is unchanged. <https://elm-test-suite.netlify.app/standard/rules/p-in-reject>

The program sends `Nothing` and then `Just "ok"` out through `echoOut`, whose type is
`Maybe String`, so they go out as JSON `null` and `"ok"`; the test harness sends each back in
through `echoIn`, whose type is `String`. `null` must be dropped and `"ok"` received. Elm 0.19.1
throws an exception for `null` instead (<https://github.com/elm/core/issues/1043>).

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, p-in-reject, p-in-accept
-- CHECK: received: "ok"
-- CHECK-NOT: received: null

port echoOut : Maybe String -> Cmd msg


port echoIn : (String -> msg) -> Sub msg


type Msg
    = Received String


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.batch [ echoOut Nothing, echoOut (Just "ok") ] )
        , update =
            \(Received s) model ->
                let
                    _ =
                        Debug.log "received" s
                in
                ( model, Cmd.none )
        , subscriptions = \_ -> echoIn Received
        }
