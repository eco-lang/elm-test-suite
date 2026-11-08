module StandardA42RemainderByZeroTest exposing (main)

{-| `remainderBy 0 x` is `0`.

<https://github.com/elm/core/issues/1072>

A Standard Definition of Elm?, ruling A42: `x // 0`, `modBy 0 x` and `remainderBy 0 x` are `0`.
<https://elm-test-suite.netlify.app/standard/basis/Basics/remainderBy>

In Elm 0.19.1 `remainderBy 0 7` is NaN, typed as an `Int`, and the NaN spreads: `remainderBy 0 7 +
1` is NaN, not `1`.

-}

-- CHECK: remainderBy 0 7 + 1 == 1: True
-- CHECK: String.fromInt (remainderBy 0 7): "0"

import Html


main =
    let
        _ =
            Debug.log "remainderBy 0 7 + 1 == 1" (remainderBy 0 7 + 1 == 1)

        _ =
            Debug.log "String.fromInt (remainderBy 0 7)" (String.fromInt (remainderBy 0 7))
    in
    Html.text "done"
