module PlatformManagerCommandTest exposing (main)

{-| A command of a manager of the platform is handed to the platform, which gives its message.

A Standard Definition of Elm?, rules p-disp-plat and p-platform: a leaf command of a manager of the
platform is dispatched to the platform, whose steps act on it. Which managers a platform has is a
parameter of the platform (ruling A83); for Elm on JavaScript they include `Random`'s
(Appendix C, Managers and Programs on a Platform). `Random.generate` with a constant generator
gives the message `7` whatever the seed. <https://elm-test-suite.netlify.app/standard/rules/p-disp-plat>

-}

-- TAGS: elm-spec, p-disp-plat, p-platform
-- CHECK: generated: 7

import Random


type Msg
    = Generated Int


main : Program () () Msg
main =
    Platform.worker
        { init = \_ -> ( (), Random.generate Generated (Random.constant 7) )
        , update =
            \(Generated n) model ->
                let
                    _ =
                        Debug.log "generated" n
                in
                ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
