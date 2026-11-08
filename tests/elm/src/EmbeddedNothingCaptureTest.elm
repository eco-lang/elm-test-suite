module EmbeddedNothingCaptureTest exposing (main)

{-| A local function that refers to a `Nothing` defined in the enclosing `let`
matches it against the `Nothing` pattern.
-}

-- TAGS: elm-spec, d-exp-lambda, d-atpat-con, d-pat-con-fail
-- CHECK: result: -1

import Html exposing (text)


main =
    let
        val =
            Nothing

        f () =
            case val of
                Just x ->
                    x

                Nothing ->
                    -1

        _ = Debug.log "result" (f ())
    in
    text "done"
