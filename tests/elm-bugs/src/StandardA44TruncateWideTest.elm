module StandardA44TruncateWideTest exposing (main)

{-| `truncate` of a Float beyond 32 bits does not wrap.

<https://github.com/elm/core/issues/1003>
<https://github.com/elm/core/issues/1079>

The Definition of Standard Elm, ruling A44: `truncate` gives the integer its argument denotes when
it lies in the Int range, and the greatest or least Int when it lies above or below.
<https://elm-test-suite.netlify.app/standard/basis/Basics/truncate>

The Int range holds every 32-bit integer, so `truncate 3.0e10` is at least `2147483647` whatever
the range. Elm 0.19.1 converts to a 32-bit integer: `truncate 3.0e10` is `-64771072`.

-}

-- CHECK: truncate 3.0e10 >= 2147483647: True
-- CHECK: truncate -3.0e10 <= -2147483648: True

import Html


main =
    let
        _ =
            Debug.log "truncate 3.0e10 >= 2147483647" (truncate 3.0e10 >= 2147483647)

        _ =
            Debug.log "truncate -3.0e10 <= -2147483648" (truncate -3.0e10 <= -2147483648)
    in
    Html.text "done"
