port module StandardA92BytesPortDeclarationTest exposing (main)

{-| A port module may declare an outgoing and an incoming port whose payload type is `Bytes`.

A Standard Definition of Elm?, ruling A92: `Bytes` is a payload type, so `Port(Bytes)` holds and
both declarations elaborate. <https://elm-test-suite.netlify.app/standard/static-modules#sec-static-modules-ports>

The ports are declared and never used: the program logs a constant and ends. Within the book's
basis no program can make a value of type `Bytes` (its functions lie outside the definition, and
no JSON flag decodes at `Bytes`), so this test checks only the declarations.
`PortPipeBytesTest` has the test driver send bytes in and checks what comes out. Elm 0.19.1
rejects a port whose type holds `Bytes`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, sm-topdec-portout, sm-topdec-portin, b:Bytes.Bytes
-- CHECK: declared: True

import Bytes exposing (Bytes)
import Platform


port echoOut : Bytes -> Cmd msg


port echoIn : (Bytes -> msg) -> Sub msg


init : () -> ( (), Cmd msg )
init _ =
    let
        _ =
            Debug.log "declared" True
    in
    ( (), Cmd.none )


main : Program () () msg
main =
    Platform.worker
        { init = init
        , update = \_ model -> ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
