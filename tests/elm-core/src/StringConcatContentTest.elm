module StringConcatContentTest exposing (main)

{-| A chain of twenty `++` operations and 100 nested `++` operations built by
recursion both produce the right text.

The chain joins the single letters `a` to `j` and `A` to `J`. The local
function `copies` joins 100 copies of `"xy"`, one `++` per copy, and the test
logs the whole 200-character result.

-}

-- TAGS: elm-spec, b:Basics.append
-- CHECK: concat20: "abcdefghijABCDEFGHIJ"
-- CHECK: concat100: "xyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxyxy"

import Html exposing (text)


copies : Int -> String
copies n =
    if n == 0 then
        ""

    else
        "xy" ++ copies (n - 1)


main =
    let
        concat20 =
            "a" ++ "b" ++ "c" ++ "d" ++ "e" ++ "f" ++ "g" ++ "h" ++ "i" ++ "j" ++ "A" ++ "B" ++ "C" ++ "D" ++ "E" ++ "F" ++ "G" ++ "H" ++ "I" ++ "J"

        concat100 =
            copies 100

        _ =
            Debug.log "concat20" concat20

        _ =
            Debug.log "concat100" concat100
    in
    text "done"
