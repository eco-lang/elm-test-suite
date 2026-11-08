module HelloTest exposing (main)

{-| The smallest program: a `main` that logs the string `"hello"` with `Debug.log` and renders it as text.
-}

-- TAGS: elm-spec, p-stat-main-view, p-dyn-main
-- CHECK: HelloTest: "hello"

import Html exposing (text)


main =
    let
        msg =
            "hello"

        _ =
            Debug.log "HelloTest" msg
    in
    text msg
