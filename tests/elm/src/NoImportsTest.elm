module NoImportsTest exposing (main)

{-| A module with no imports elaborates and runs, with the default imports only.

A Standard Definition of Elm?, rules sm-imports-empty and dm-imports-empty: an empty sequence of
imports adds nothing to the initial basis. The program is a worker whose `init` gives `Cmd.none`,
an empty dispatch (rule p-disp-empty). <https://elm-test-suite.netlify.app/standard/rules/sm-imports-empty>

-}

-- TAGS: elm-spec, sm-imports-empty, dm-imports-empty, p-disp-empty
-- CHECK: no imports: 3

main : Program () () ()
main =
    Platform.worker
        { init =
            \_ ->
                let
                    _ =
                        Debug.log "no imports" (1 + 2)
                in
                ( (), Cmd.none )
        , update = \_ model -> ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
