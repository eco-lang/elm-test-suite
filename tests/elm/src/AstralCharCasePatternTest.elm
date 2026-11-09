module AstralCharCasePatternTest exposing (main)

{-| A `case` on a `Char` matches a pattern above U+FFFF, `'\u{1F600}'`, against the same character written as an escape or as the character itself.

A pattern in the Basic Multilingual Plane, `'\u{20AC}'`, still matches `'€'`, and
`'a'` falls through to the wildcard. That a lone low surrogate made by `Char.fromCode` does not
match the U+1F600 pattern is checked by `elm-core`'s `CharFromCodeLoneSurrogatePatternTest`.

-}

-- TAGS: elm-spec, d-atpat-scon, d-atpat-scon-fail
-- CHECK: a: "other"
-- CHECK: euro: "euro"
-- CHECK: escape: "grin"
-- CHECK: literal: "grin"

import Html exposing (text)


classify : Char -> String
classify c =
    case c of
        '\u{1F600}' ->
            "grin"

        '\u{20AC}' ->
            "euro"

        _ ->
            "other"


main =
    let
        _ =
            Debug.log "a" (classify 'a')

        _ =
            Debug.log "euro" (classify '€')

        _ =
            Debug.log "escape" (classify '\u{1F600}')

        _ =
            Debug.log "literal" (classify '😀')
    in
    text "done"
