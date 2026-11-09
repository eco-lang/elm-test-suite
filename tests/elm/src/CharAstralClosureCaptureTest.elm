module CharAstralClosureCaptureTest exposing (main)

{-| An astral `Char` (code point above 0xFFFF) referred to by a lambda, or
supplied as the first argument of a partially applied function, keeps its code
point when the function is called later.

`addCode` returns a lambda that adds the character's code to its argument, and
`giveBack` returns a lambda that returns the character. `pairUp '😀'` is
partially applied, and the function is applied to 1 and to 2, each resulting pair summed.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character (Figure 1, Escape Sequences), as does the
character itself written in a constant. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode> A closure keeps the value it
captured (rules d-exp-lambda and d-app-closure).

-}

-- TAGS: elm-spec, b:Char.toCode, d-atexp-scon, d-exp-lambda, d-app-closure
-- CHECK: cap_add: [128513,98]
-- CHECK: cap_return: [128512,119070]
-- CHECK: pap_pairs: [128513,128514]

import Html exposing (text)


addCode : Char -> (Int -> Int)
addCode c =
    \n -> n + Char.toCode c


giveBack : Char -> (() -> Char)
giveBack c =
    \() -> c


pairUp : Char -> Int -> ( Int, Char )
pairUp c n =
    ( n, c )


sumPair : ( Int, Char ) -> Int
sumPair ( n, c ) =
    n + Char.toCode c


main =
    let
        addEmoji =
            addCode '😀'

        addA =
            addCode 'a'

        giveEmoji =
            giveBack '😀'

        giveClef =
            giveBack '\u{1D11E}'

        withEmoji =
            pairUp '😀'

        _ =
            Debug.log "cap_add" [ addEmoji 1, addA 1 ]

        _ =
            Debug.log "cap_return" [ Char.toCode (giveEmoji ()), Char.toCode (giveClef ()) ]

        _ =
            Debug.log "pap_pairs" [ sumPair (withEmoji 1), sumPair (withEmoji 2) ]
    in
    text "done"
