module StandardA45IntNegativeZeroTest exposing (main)

{-| Int has one zero: no Int operation gives a negative zero.

A Standard Definition of Elm?, ruling A45: Int has one zero, so `toFloat` of any Int zero is `+0`
and `1 / toFloat` of it is `+Infinity`. <https://elm-test-suite.netlify.app/standard/basis/Basics/negate>

In Elm 0.19.1 `negate 0`, `0 * -1`, `modBy 4 -4`, `remainderBy 4 -4`, `round -0.4` and
`ceiling -0.5` give a negative zero typed as an `Int`; equality does not see it, but `1 /
toFloat` of it is `-Infinity`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.negate, b:Basics.mul, b:Basics.modBy, b:Basics.remainderBy, b:Basics.round, b:Basics.ceiling
-- CHECK: negate 0: True
-- CHECK: 0 * -1: True
-- CHECK: modBy 4 -4: True
-- CHECK: remainderBy 4 -4: True
-- CHECK: round -0.4: True
-- CHECK: ceiling -0.5: True

import Html


positiveZero : Int -> Bool
positiveZero n =
    n == 0 && 1 / toFloat n > 0


main =
    let
        _ =
            Debug.log "negate 0" (positiveZero (negate 0))

        _ =
            Debug.log "0 * -1" (positiveZero (0 * -1))

        _ =
            Debug.log "modBy 4 -4" (positiveZero (modBy 4 -4))

        _ =
            Debug.log "remainderBy 4 -4" (positiveZero (remainderBy 4 -4))

        _ =
            Debug.log "round -0.4" (positiveZero (round -0.4))

        _ =
            Debug.log "ceiling -0.5" (positiveZero (ceiling -0.5))
    in
    Html.text "done"
