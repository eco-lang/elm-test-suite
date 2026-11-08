module StandardA42ModByZeroTest exposing (main)

{-| `modBy 0 x` is `0`.

<https://github.com/elm/core/issues/1147>
<https://github.com/elm/core/issues/1072>

The Definition of Standard Elm, ruling A42: `x // 0`, `modBy 0 x` and `remainderBy 0 x` are `0`,
so that no evaluation ends in a run-time error. <https://elm-test-suite.netlify.app/standard/basis/Basics/modBy>

Elm 0.19.1 stops the program: "Cannot perform mod 0. Division by zero error." (The result is
compared with `1` after adding `1`: Elm 0.19.1 compiles `x == 0` as `!x`, elm/core #1115.)

-}

-- CHECK: modBy 0 7 + 1 == 1: True
-- CHECK: modBy 0 -7 + 1 == 1: True

import Html


main =
    let
        _ =
            Debug.log "modBy 0 7 + 1 == 1" (modBy 0 7 + 1 == 1)

        _ =
            Debug.log "modBy 0 -7 + 1 == 1" (modBy 0 -7 + 1 == 1)
    in
    Html.text "done"
