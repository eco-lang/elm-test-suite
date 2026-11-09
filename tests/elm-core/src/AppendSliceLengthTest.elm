module AppendSliceLengthTest exposing (main)

{-| `++` of long strings and of slices, observed with `String.length` and `String.slice`.

`ropeStr` is a 140,000-character string, 70,000 `a`s appended to 70,000 `b`s, built with
`String.repeat`. The test logs its length, two slices of `"hello"` appended, and the two
characters on either side of the join in `ropeStr`. The same appends observed without library
functions are checked by AppendTypeSplitTest.

-}

-- CHECK: ropeLen: 140000
-- CHECK: sliceAppend: "llohel"
-- CHECK: ropeThenSlice: "ab"

import Html exposing (text)


{-| A 140,000-character string: 70,000 `a`s appended to 70,000 `b`s.
-}
ropeStr : String
ropeStr =
    String.repeat 70000 "a" ++ String.repeat 70000 "b"


main : Html.Html msg
main =
    let
        _ =
            Debug.log "ropeLen" (String.length ropeStr)

        _ =
            Debug.log "sliceAppend" (String.slice 2 5 "hello" ++ String.slice 0 3 "hello")

        _ =
            Debug.log "ropeThenSlice" (String.slice 69999 70001 ropeStr)
    in
    text "done"
