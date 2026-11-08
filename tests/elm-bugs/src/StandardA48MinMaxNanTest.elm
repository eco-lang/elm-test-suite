module StandardA48MinMaxNanTest exposing (main)

{-| Float `min` and `max` are IEEE 754-2019 minimum and maximum, whatever the order of the arguments.

A Standard Definition of Elm?, ruling A48: at floats, `min` and `max` of a NaN are NaN, and `-0`
is below `+0`. <https://elm-test-suite.netlify.app/standard/basis/Basics/min>

Elm 0.19.1 uses `if lt x y then x else y`, so the answer depends on the order of the arguments:
`min nan 1` is `1` and `min 1 nan` is NaN, and `min 0 -0` is `-0` but `min -0 0` is `0`.

-}

-- CHECK: min nan 1 is NaN: True
-- CHECK: min 1 nan is NaN: True
-- CHECK: max nan 1 is NaN: True
-- CHECK: max 1 nan is NaN: True
-- CHECK: min 0 -0 is -0: True
-- CHECK: min -0 0 is -0: True
-- CHECK: max 0 -0 is +0: True
-- CHECK: max -0 0 is +0: True

import Html


nan : Float
nan =
    0 / 0


zero : Float
zero =
    0


negativeZero : Float
negativeZero =
    -zero


main =
    let
        _ =
            Debug.log "min nan 1 is NaN" (isNaN (min nan 1))

        _ =
            Debug.log "min 1 nan is NaN" (isNaN (min 1 nan))

        _ =
            Debug.log "max nan 1 is NaN" (isNaN (max nan 1))

        _ =
            Debug.log "max 1 nan is NaN" (isNaN (max 1 nan))

        _ =
            Debug.log "min 0 -0 is -0" (1 / min zero negativeZero < 0)

        _ =
            Debug.log "min -0 0 is -0" (1 / min negativeZero zero < 0)

        _ =
            Debug.log "max 0 -0 is +0" (1 / max zero negativeZero > 0)

        _ =
            Debug.log "max -0 0 is +0" (1 / max negativeZero zero > 0)
    in
    Html.text "done"
