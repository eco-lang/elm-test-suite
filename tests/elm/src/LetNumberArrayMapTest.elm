module LetNumberArrayMapTest exposing (main)

{-| An unannotated `let`-bound `Array` of number literals is mapped with a function
that uses each element as a Float: `x * 1.5` then `round` turns `[30, 40]` into
`[45,60]`.

Tagged `elm-unspecced`: `Array.fromList`, `Array.map` and `Array.toList` are library functions of
`Array`, which A Standard Definition of Elm? puts outside the definition (Appendix C, Library
functions), so it does not decide this program's output. The rules of the `number` literals are
checked within the definition by the `LetNumber` tests over lists, records, tuples and custom
types; this test keeps a literal crossing elm/core's array code.

-}

-- TAGS: elm-unspecced
-- CHECK: array: [45,60]

import Array
import Html exposing (text)


main =
    let
        arr =
            Array.fromList [ 30, 40 ]

        result =
            Array.toList (Array.map (\x -> round (x * 1.5)) arr)

        _ =
            Debug.log "array" result
    in
    text "done"
