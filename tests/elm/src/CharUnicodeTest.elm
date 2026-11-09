module CharUnicodeTest exposing (main)

{-| `Char.toCode` of non-ASCII character literals written as `\u{...}` escapes
gives their code points: 955 for U+03BB and 8364 for U+20AC.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character (Figure 1, Escape Sequences), as does the
character itself written in a constant. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode>

-}

-- TAGS: elm-spec, b:Char.toCode, fig:core-escapes, d-atexp-scon
-- CHECK: code1: 955
-- CHECK: code2: 8364

import Html exposing (text)


main =
    let
        -- Greek lambda
        _ = Debug.log "code1" (Char.toCode '\u{03BB}')
        -- Euro sign
        _ = Debug.log "code2" (Char.toCode '\u{20AC}')
    in
    text "done"
