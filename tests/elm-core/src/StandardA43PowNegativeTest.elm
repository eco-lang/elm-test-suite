module StandardA43PowNegativeTest exposing (main)

{-| Int `^` with a negative exponent: `1 ^ n` is `1`, `(-1) ^ n` is `1` or `-1` by the parity of
`n`, and any other base gives `0`.

A Standard Definition of Elm?, ruling A43: at Int, `b ^ e` with `e < 0` is the integer part of the
exact power, so it is `0` except when `b` is `1` or `-1`, where the power is exact.
<https://elm-test-suite.netlify.app/standard/basis/Basics/pow>

Elm 0.19.1 computes `^` with JavaScript's `Math.pow`, so `2 ^ -1` is `0.5` and `0 ^ -1` is
`Infinity`, neither of them an Int. (Those two are compared with `1` after adding `1`, so that a
CHECK line cannot match the start of a longer number.)

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.pow
-- CHECK: 1 ^ -1: 1
-- CHECK: (-1) ^ -3: -1
-- CHECK: (-1) ^ -2: 1
-- CHECK: 2 ^ -1 + 1 == 1: True
-- CHECK: 0 ^ -1 + 1 == 1: True

import Html


main =
    let
        _ =
            Debug.log "1 ^ -1" (1 ^ -1)

        _ =
            Debug.log "(-1) ^ -3" ((-1) ^ -3)

        _ =
            Debug.log "(-1) ^ -2" ((-1) ^ -2)

        _ =
            Debug.log "2 ^ -1 + 1 == 1" (2 ^ -1 + 1 == 1)

        _ =
            Debug.log "0 ^ -1 + 1 == 1" (0 ^ -1 + 1 == 1)
    in
    Html.text "done"
