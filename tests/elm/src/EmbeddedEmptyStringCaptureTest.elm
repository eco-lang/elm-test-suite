module EmbeddedEmptyStringCaptureTest exposing (main)

{-| A local function that refers to an empty string defined in the enclosing
`let` sees it as empty: it is equal to `""`, and the captured string it returns
is `""`.
-}

-- TAGS: elm-spec, d-exp-lambda, d-app-closure, d-valbind-pat
-- CHECK: isEmpty: True
-- CHECK: captured: ""

import Html exposing (text)


main =
    let
        s =
            ""

        f () =
            ( s == "", s )

        ( isEmpty, captured ) =
            f ()

        _ = Debug.log "isEmpty" isEmpty
        _ = Debug.log "captured" captured
    in
    text "done"
