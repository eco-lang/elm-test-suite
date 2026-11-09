module CharFromCodeLoneSurrogatePatternTest exposing (main)

{-| A lone low surrogate made by `Char.fromCode`, `Char.fromCode 0xDE00`, does not match the
pattern `'\u{1F600}'`, of which it is the second UTF-16 code unit; the character
`Char.fromCode 0x1F600` does.

`Char.fromCode` is library, outside A Standard Definition of Elm?, and what it gives for a
surrogate code point is not a character the book knows (a surrogate escape is not a character,
ruling A8). Elm/JS represents a Char as a JavaScript string, so the check guards against a
pattern matching part of one: a lone surrogate is a different `Char` from the character it is
half of.

-}

-- CHECK: lowSurrogate: "other"
-- CHECK: fromCode: "grin"

import Html exposing (text)


classify : Char -> String
classify c =
    case c of
        '\u{1F600}' ->
            "grin"

        _ ->
            "other"


main =
    let
        _ =
            Debug.log "lowSurrogate" (classify (Char.fromCode 0xDE00))

        _ =
            Debug.log "fromCode" (classify (Char.fromCode 0x0001F600))
    in
    text "done"
