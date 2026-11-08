module StandardA72AbsentFlagsTest exposing (main)

{-| A program given no flags starts with flags `null`: `Maybe` flags are `Nothing`.

A Standard Definition of Elm?, ruling A72: when the host gives no flags, the flags are the JSON
value `null`. <https://elm-test-suite.netlify.app/standard/rules/p-init>

This test is started without flags (no `-- FLAGS:` line). Elm 0.19.1 decodes `undefined`, which a
`Maybe Int` decoder rejects, and stops: "Problem with the flags given to your Elm program on
initialization."

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, p-init, e-dec-nothing
-- CHECK: flags: Nothing


init : Maybe Int -> ( (), Cmd () )
init flags =
    let
        _ =
            Debug.log "flags" flags
    in
    ( (), Cmd.none )


main : Program (Maybe Int) () ()
main =
    Platform.worker
        { init = init
        , update = \_ model -> ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
