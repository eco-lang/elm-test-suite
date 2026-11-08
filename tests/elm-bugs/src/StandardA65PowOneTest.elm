module StandardA65PowOneTest exposing (main)

{-| Float `1 ^ y` is `1` for every `y`, and `(-1) ^ y` is `1` for an infinite `y`.

The Definition of Standard Elm, ruling A65: Float `pow` is IEEE 754-2019 `pow`, under which `1 ^ y`
is `1` even when `y` is an infinity or NaN, and `-1 ^ ±Infinity` is `1`.
<https://elm-test-suite.netlify.app/standard/basis/Basics/pow>

Elm 0.19.1 uses JavaScript's `Math.pow`, which gives NaN for all three.

-}

-- CHECK: 1 ^ inf == 1: True
-- CHECK: 1 ^ nan == 1: True
-- CHECK: (-1) ^ inf == 1: True

import Html


one : Float
one =
    1


nan : Float
nan =
    0 / 0


inf : Float
inf =
    1 / 0


main =
    let
        _ =
            Debug.log "1 ^ inf == 1" (one ^ inf == 1)

        _ =
            Debug.log "1 ^ nan == 1" (one ^ nan == 1)

        _ =
            Debug.log "(-1) ^ inf == 1" ((-one) ^ inf == 1)
    in
    Html.text "done"
