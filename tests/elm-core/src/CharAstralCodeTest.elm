module CharAstralCodeTest exposing (main)

{-| `Char.fromCode` and `Char.toCode` round-trip Unicode code points, including
astral ones (above 0xFFFF) and the largest, 0x10FFFF.

The test round-trips U+20AC, U+1F600, U+1D11E and U+10FFFF. What `Char.fromCode` gives for a code
below 0 or above 0x10FFFF is the implementation's choice; `CharFromCodeWideIntTest` checks it.

A Standard Definition of Elm?, the basis entries Char.fromCode and Char.toCode: for a Unicode
scalar value n, `Char.fromCode n` is the character with code point n, and its code is n.
<https://elm-test-suite.netlify.app/standard/basis/Char/fromCode>

-}

-- TAGS: elm-spec, b:Char.fromCode, b:Char.toCode
-- CHECK: bmp: 8364
-- CHECK: emoji: 128512
-- CHECK: clef: 119070
-- CHECK: maxcp: 1114111

import Char
import Html exposing (text)


main =
    let
        _ =
            Debug.log "bmp" (Char.toCode (Char.fromCode 0x20AC))

        _ =
            Debug.log "emoji" (Char.toCode (Char.fromCode 0x0001F600))

        _ =
            Debug.log "clef" (Char.toCode (Char.fromCode 0x0001D11E))

        _ =
            Debug.log "maxcp" (Char.toCode (Char.fromCode 0x0010FFFF))

    in
    text "done"
