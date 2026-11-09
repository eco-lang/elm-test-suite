module AstralCharLiteralTest exposing (main)

{-| A `Char` literal above U+FFFF has its full code point: `'\u{1F600}'` is 128512, and is the
same character as `'😀'` written directly.

A literal in the Basic Multilingual Plane, `'\u{20AC}'`, is checked as well.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character (Figure 1, Escape Sequences), as does the
character itself written in a constant. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode>

-}

-- TAGS: elm-spec, b:Char.toCode, fig:core-escapes, core-escape-unicode, d-atexp-scon, b:Basics.eq
-- CHECK: astral: 128512
-- CHECK: bmp: 8364
-- CHECK: sameAsWritten: True

import Html exposing (text)


main =
    let
        _ =
            Debug.log "astral" (Char.toCode '\u{1F600}')

        _ =
            Debug.log "bmp" (Char.toCode '\u{20AC}')

        _ =
            Debug.log "sameAsWritten" ('\u{1F600}' == '😀')
    in
    text "done"
