module StandardA41IntDivisionWideTest exposing (main)

{-| `a // 1` is `a`, also for an `a` beyond 32 bits.

A Standard Definition of Elm?, ruling A41: for `b /= 0`, `a // b` is the truncated quotient
normalised into the Int range. <https://elm-test-suite.netlify.app/standard/basis/Basics/idiv>

An integer constant denotes its value normalised into the Int range, so whatever the range both
sides below are the same Int. Elm 0.19.1 converts every quotient to a 32-bit integer:
`5000000000 // 1` is `705032704`.

-}

-- TAGS: elm19-bug
-- CHECK: 5000000000 // 1 == 5000000000: True
-- CHECK: -5000000000 // 1 == -5000000000: True

import Html


main =
    let
        _ =
            Debug.log "5000000000 // 1 == 5000000000" (5000000000 // 1 == 5000000000)

        _ =
            Debug.log "-5000000000 // 1 == -5000000000" (-5000000000 // 1 == -5000000000)
    in
    Html.text "done"
