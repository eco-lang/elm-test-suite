module CharAstralRecordFieldTest exposing (main)

{-| An astral `Char` (code point above 0xFFFF) in a record field keeps its code
point, next to an `Int` field and after a record update, and a record holding
one is equal to a record literal with the same fields.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode>
-}

-- TAGS: elm-spec, d-atexp-update, d-atexp-record, b:Char.toCode, fig:core-escapes
-- CHECK: rec_c: 128512
-- CHECK: rec_n: 7
-- CHECK: rec_updated: 119070
-- CHECK: rec_eq: True


import Html exposing (text)


type alias Glyph =
    { c : Char, n : Int }


mk : Char -> Int -> Glyph
mk c n =
    { c = c, n = n }


main =
    let
        g =
            mk '😀' 7

        h =
            { g | c = '\u{1D11E}' }

        _ =
            Debug.log "rec_c" (Char.toCode g.c)

        _ =
            Debug.log "rec_n" g.n

        _ =
            Debug.log "rec_updated" (Char.toCode h.c)

        _ =
            Debug.log "rec_eq" (g == { c = '😀', n = 7 })
    in
    text "done"
