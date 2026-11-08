module CaseDefaultTest exposing (main)

{-| A case on Int with one literal branch and a wildcard sends every other value to the wildcard.
-}

-- TAGS: elm-spec, d-atpat-scon, d-atpat-scon-fail, d-atpat-wild
-- CHECK: default1: "special"
-- CHECK: default2: "normal"
-- CHECK: default3: "normal"

import Html exposing (text)


classify n =
    case n of
        42 -> "special"
        _ -> "normal"


main =
    let
        _ = Debug.log "default1" (classify 42)
        _ = Debug.log "default2" (classify 1)
        _ = Debug.log "default3" (classify 100)
    in
    text "done"
