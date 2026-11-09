module CharToCodeTest exposing (main)

{-| `Char.toCode` gives the code points 65, 97 and 48 for `'A'`, `'a'` and `'0'`.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode>

-}

-- TAGS: elm-spec, b:Char.toCode
-- CHECK: code1: 65
-- CHECK: code2: 97
-- CHECK: code3: 48

import Char
import Html exposing (text)


main =
    let
        _ = Debug.log "code1" (Char.toCode 'A')
        _ = Debug.log "code2" (Char.toCode 'a')
        _ = Debug.log "code3" (Char.toCode '0')
    in
    text "done"
