module StandardA40IntOverflowTest exposing (main)

{-| Int `+`, `-` and `*` give an Int, never an infinity or NaN, however large the exact result.

A Standard Definition of Elm?, ruling A40: Int addition, subtraction and multiplication give the
exact result normalised into the Int range, and an Int is always a member of that range.
<https://elm-test-suite.netlify.app/standard/basis/Basics/mul>

Whatever an implementation's Int range, `big` is some Int `m`, `big * big` some Int `p`, and
`p - p + 1` is `1`; likewise for `huge + huge`. In Elm 0.19.1 an Int is a double:
`10 ^ 200 * 10 ^ 200` and `10 ^ 308 + 10 ^ 308` overflow to `Infinity`, `Infinity - Infinity` is
NaN, and NaN + 1 is not 1.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec
-- CHECK: big * big - big * big + 1 == 1: True
-- CHECK: huge + huge - (huge + huge) + 1 == 1: True

import Html


big : Int
big =
    10 ^ 200


huge : Int
huge =
    10 ^ 308


main =
    let
        _ =
            Debug.log "big * big - big * big + 1 == 1" (big * big - big * big + 1 == 1)

        _ =
            Debug.log "huge + huge - (huge + huge) + 1 == 1" (huge + huge - (huge + huge) + 1 == 1)
    in
    Html.text "done"
