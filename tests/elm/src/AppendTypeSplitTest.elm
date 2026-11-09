module AppendTypeSplitTest exposing (main)

{-| `++` gives the right result on `String`s and `List`s, including empty operands, long strings, nested appends, and a function whose type is `appendable`.

Each of `String` and `List` is appended with an empty operand on the left, on
the right, and on both sides. The string cases also compare two 131,072-character
strings built by `++` in different ways: equal when they hold the same characters,
and not equal when only the last one differs. The list cases also append a list
computed element by element. Slices and the length of a long string, which only
library functions can observe, are checked by AppendSliceLengthTest.

-}

-- TAGS: elm-spec, b:Basics.append
-- CHECK: strs: "foobar"
-- CHECK: strEmptyR: "foo"
-- CHECK: strEmptyL: "foo"
-- CHECK: strBothEmpty: ""
-- CHECK: ropeEq: True
-- CHECK: ropeNeq: False
-- CHECK: lists: [1,2,3,4]
-- CHECK: listEmptyR: [1,2]
-- CHECK: listEmptyL: [1,2]
-- CHECK: listBothEmpty: []
-- CHECK: chunkAppend: [2,4,6,1]
-- CHECK: nested: "abcdef"
-- CHECK: polyStr: "hihi"
-- CHECK: polyList: [7,7]

import Html exposing (text)


{-| Two string literals appended.
-}
strs : String
strs =
    "foo" ++ "bar"


{-| `s` appended to itself `n` times over: 2^n copies of `s`.
-}
doubled : Int -> String -> String
doubled n s =
    if n <= 0 then
        s

    else
        doubled (n - 1) (s ++ s)


{-| A 131,072-character string: 65,536 `a`s appended to 65,536 `b`s.
-}
ropeStr : String
ropeStr =
    doubled 16 "a" ++ doubled 16 "b"


{-| The same characters as `ropeStr`, appended in another grouping: the `b`s in two halves.
-}
ropeStr2 : String
ropeStr2 =
    doubled 16 "a" ++ (doubled 15 "b" ++ doubled 15 "b")


{-| `ropeStr` with its last character changed: the `b`s end in a `c`.
-}
ropeStrLastC : String
ropeStrLastC =
    doubled 16 "a" ++ (doubled 15 "b" ++ (doubled 14 "b" ++ (doubled 13 "b" ++ (doubled 12 "b" ++ (doubled 11 "b" ++ (doubled 10 "b" ++ (doubled 9 "b" ++ (doubled 8 "b" ++ (doubled 7 "b" ++ (doubled 6 "b" ++ (doubled 5 "b" ++ (doubled 4 "b" ++ (doubled 3 "b" ++ (doubled 2 "b" ++ (doubled 1 "b" ++ ("b" ++ "c"))))))))))))))))


{-| Two list literals appended.
-}
lists : List Int
lists =
    [ 1, 2 ] ++ [ 3, 4 ]


{-| A list computed element by element appended to a list literal.
-}
chunkAppend : List Int
chunkAppend =
    [ 1 * 2, 2 * 2, 3 * 2 ] ++ [ 1 ]


{-| Three strings appended, where the left operand is itself an append.
-}
nested : String
nested =
    ("ab" ++ "cd") ++ "ef"


{-| Returns `x` appended to itself. Its type is `appendable`, and the test uses it
at `String` and at `List`.
-}
twice : appendable -> appendable
twice x =
    x ++ x


main : Html.Html msg
main =
    let
        _ =
            Debug.log "strs" strs

        _ =
            Debug.log "strEmptyR" ("foo" ++ "")

        _ =
            Debug.log "strEmptyL" ("" ++ "foo")

        _ =
            Debug.log "strBothEmpty" ("" ++ "")

        _ =
            Debug.log "ropeEq" (ropeStr == ropeStr2)

        _ =
            Debug.log "ropeNeq" (ropeStr == ropeStrLastC)

        _ =
            Debug.log "lists" lists

        _ =
            Debug.log "listEmptyR" ([ 1, 2 ] ++ [])

        _ =
            Debug.log "listEmptyL" ([] ++ [ 1, 2 ])

        _ =
            Debug.log "listBothEmpty" ([] ++ [])

        _ =
            Debug.log "chunkAppend" chunkAppend

        _ =
            Debug.log "nested" nested

        _ =
            Debug.log "polyStr" (twice "hi")

        _ =
            Debug.log "polyList" (twice [ 7 ])
    in
    text "done"
