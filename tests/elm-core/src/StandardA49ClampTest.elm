module StandardA49ClampTest exposing (main)

{-| `clamp lo hi x`: at Float it is `min (max x lo) hi`, with the IEEE 754 `maximum` and `minimum`
that propagate NaN and order `-0` below `+0`; at Int it is the text of elm/core.

A Standard Definition of Elm?, ruling A49. These are the book's examples: at Float, `clamp 10 0 5`
is `+0` (the bounds the wrong way round give `hi`), `clamp nan 1 0.5` is NaN, `clamp 0 1 -0` is
`+0` and `clamp -1 -0 0` is `-0`; at Int, `clamp 10 0 5` is `10`, as elm/core's text gives.
<https://elm-test-suite.netlify.app/standard/basis/Basics/clamp>

The float results are tested without printing a float: a value is NaN when it is not equal to
itself, and a zero's sign is the sign of `1` divided by it.

Elm 0.19.1 computes `clamp` at Float by elm/core's text too, so it gives `10`, `0.5`, `-0` and `0`
for the four float examples.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.clamp
-- CHECK: clamp 10 0 5 at Float is +0: True
-- CHECK: clamp nan 1 0.5 is NaN: True
-- CHECK: clamp 0 1 -0 is +0: True
-- CHECK: clamp -1 -0 0 is -0: True
-- CHECK: clamp 10 0 5 at Int: 10
-- CHECK: clamp 10 0 20 at Int: 0
-- CHECK: clamp 0 10 -5 at Int: 0
-- CHECK: clamp 0 10 15 at Int: 10
-- CHECK: clamp 0 10 7 at Int: 7

import Html


nan : Float
nan =
    0 / 0


negZero : Float
negZero =
    -0


isNotSelf : Float -> Bool
isNotSelf x =
    x /= x


isPositiveZero : Float -> Bool
isPositiveZero x =
    x == 0 && 1 / x > 0


isNegativeZero : Float -> Bool
isNegativeZero x =
    x == 0 && 1 / x < 0


main =
    let
        _ =
            Debug.log "clamp 10 0 5 at Float is +0" (isPositiveZero (clamp 10 0 5))

        _ =
            Debug.log "clamp nan 1 0.5 is NaN" (isNotSelf (clamp nan 1 0.5))

        _ =
            Debug.log "clamp 0 1 -0 is +0" (isPositiveZero (clamp 0 1 negZero))

        _ =
            Debug.log "clamp -1 -0 0 is -0" (isNegativeZero (clamp -1 negZero 0))

        _ =
            Debug.log "clamp 10 0 5 at Int" (clamp 10 0 5)

        _ =
            Debug.log "clamp 10 0 20 at Int" (clamp 10 0 20)

        _ =
            Debug.log "clamp 0 10 -5 at Int" (clamp 0 10 -5)

        _ =
            Debug.log "clamp 0 10 15 at Int" (clamp 0 10 15)

        _ =
            Debug.log "clamp 0 10 7 at Int" (clamp 0 10 7)
    in
    Html.text "done"
