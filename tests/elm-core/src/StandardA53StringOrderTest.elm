module StandardA53StringOrderTest exposing (main)

{-| Strings are ordered character by character, by code point.

A Standard Definition of Elm?, ruling A53: `compare` on strings is lexicographic over their
characters, ordered by `toCode`. <https://elm-test-suite.netlify.app/standard/appendix-dynamic-basis#sec-appendix-dynamic-basis-order>

`"😀"` (U+1F600) is above `"ﬀ"` (U+FB00). Elm 0.19.1 compares UTF-16 code units, so it puts `"😀"`
first, and sorts the list the other way round.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.compare, b:Basics.gt, b:String.String
-- CHECK: compare "😀" "ﬀ": GT
-- CHECK: "😀" > "ﬀ": True
-- CHECK: sorted: ["ﬀ","😀"]

import Html


main =
    let
        _ =
            Debug.log "compare \"😀\" \"ﬀ\"" (compare "😀" "ﬀ")

        _ =
            Debug.log "\"😀\" > \"ﬀ\"" ("😀" > "ﬀ")

        _ =
            Debug.log "sorted" (List.sort [ "😀", "ﬀ" ])
    in
    Html.text "done"
