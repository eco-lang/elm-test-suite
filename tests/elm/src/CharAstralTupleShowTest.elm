module CharAstralTupleShowTest exposing (main)

{-| `Debug.log` prints tuples that hold astral `Char`s (code points above 0xFFFF) with the
characters themselves: `(1,'😀')` and `('a','𝄞',2)`.

The code points the tuples keep are checked by `CharAstralTupleTest`.

A Standard Definition of Elm? does not decide this test: `Debug.log l v` evaluates to `v`, and any
output it makes, its text, its order and whether it is made at all, is outside the definition
(ruling A62).

-}

-- TAGS: elm-unspecced
-- CHECK: tup2_show: (1,'😀')
-- CHECK: tup3_show: ('a','𝄞',2)

import Html exposing (text)


main =
    let
        _ =
            Debug.log "tup2_show" ( 1, '😀' )

        _ =
            Debug.log "tup3_show" ( 'a', '\u{1D11E}', 2 )
    in
    text "done"
