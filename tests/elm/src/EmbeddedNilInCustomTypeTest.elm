module EmbeddedNilInCustomTypeTest exposing (main)

{-| An empty list stored in a custom type constructor and taken back out by a
`case` is still empty, with length 0.

Emptiness is tested by a `case` on the list, and the length is computed by a
local `length` written by pattern matching.
-}

-- TAGS: elm-spec, s-atexp-nil, d-app-con, d-pat-con
-- CHECK: isEmpty: True
-- CHECK: len: 0

import Html exposing (text)


type Holder a
    = Hold a
    | Empty


length : List a -> Int
length xs =
    case xs of
        [] ->
            0

        _ :: rest ->
            1 + length rest


main =
    let
        h =
            Hold []

        list =
            case h of
                Hold xs ->
                    xs

                Empty ->
                    []

        isEmpty =
            case list of
                [] ->
                    True

                _ ->
                    False

        _ = Debug.log "isEmpty" isEmpty
        _ = Debug.log "len" (length list)
    in
    text "done"
