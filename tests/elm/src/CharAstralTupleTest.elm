module CharAstralTupleTest exposing (main)

{-| An astral `Char` (code point above 0xFFFF) in a pair and in a 3-tuple keeps
its code point when read back with a tuple pattern, in a function's argument and in a
destructuring `let`. How `Debug.log` prints such tuples is checked by `CharAstralTupleShowTest`.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character (Figure 1, Escape Sequences), as does the
character itself written in a constant. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode> A tuple holds the values it was built
from (rules d-atexp-tuple and d-atpat-tuple).

-}

-- TAGS: elm-spec, b:Char.toCode, d-atexp-scon, d-atexp-tuple, d-atpat-tuple, d-valbind-pat
-- CHECK: tup2_code: 128512
-- CHECK: tup3_code: 119070

import Html exposing (text)


pair : Int -> Char -> ( Int, Char )
pair n c =
    ( n, c )


secondCode : ( Int, Char ) -> Int
secondCode ( _, c ) =
    Char.toCode c


main =
    let
        t2 =
            pair 1 '😀'

        t3 =
            ( 'a', '\u{1D11E}', 2 )

        ( _, c3, _ ) =
            t3

        _ =
            Debug.log "tup2_code" (secondCode t2)

        _ =
            Debug.log "tup3_code" (Char.toCode c3)
    in
    text "done"
