module StandardA46CompareNanTest exposing (main)

{-| `compare` is a total order on Float: NaN is above every other float and equal to NaN.

A Standard Definition of Elm?, ruling A46: at floats, `compare x y` is `EQ` if both are NaN, `GT`
if only `x` is NaN, and `LT` if only `y` is NaN. <https://elm-test-suite.netlify.app/standard/basis/Basics/compare>

In Elm 0.19.1 `compare` with a NaN argument is always `GT`, so `compare 1 nan` and `compare nan
nan` are `GT`, and sorting with `compare` has no defined result.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec
-- CHECK: compare 1 nan: LT
-- CHECK: compare nan nan: EQ
-- CHECK: compare nan 1: GT

import Html


nan : Float
nan =
    0 / 0


main =
    let
        _ =
            Debug.log "compare 1 nan" (compare 1 nan)

        _ =
            Debug.log "compare nan nan" (compare nan nan)

        _ =
            Debug.log "compare nan 1" (compare nan 1)
    in
    Html.text "done"
