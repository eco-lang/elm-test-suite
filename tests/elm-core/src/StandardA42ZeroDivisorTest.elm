module StandardA42ZeroDivisorTest exposing (main)

{-| `3 // 0`, `modBy 0 3` and `remainderBy 0 3` are all `0`: the examples A Standard Definition of
Elm? gives for ruling A42 in its initial dynamic basis.

Ruling A42: an integer division, `modBy` or `remainderBy` whose divisor is `0` gives `0`, so that no
evaluation ends in a run-time error. <https://elm-test-suite.netlify.app/standard/basis/Basics/idiv>

Elm 0.19.1 gives `0` for `3 // 0`, then stops the program at `modBy 0 3` ("Cannot perform mod 0.
Division by zero error."), so the last two checks are not printed.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.idiv, b:Basics.modBy, b:Basics.remainderBy
-- CHECK: 3 // 0: 0
-- CHECK: modBy 0 3: 0
-- CHECK: remainderBy 0 3: 0

import Html


main =
    let
        _ =
            Debug.log "3 // 0" (3 // 0)

        _ =
            Debug.log "modBy 0 3" (modBy 0 3)

        _ =
            Debug.log "remainderBy 0 3" (remainderBy 0 3)
    in
    Html.text "done"
