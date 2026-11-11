module CoreIssue1080ClampNanTest exposing (main)

{-| `clamp -100 100` of NaN returns NaN.

<https://github.com/elm/core/issues/1080>

`clamp` is documented as returning `low` when the number is below it, `high` when above it, and
the number otherwise. Both comparisons are false for NaN, so the result must be NaN, as the book
also gives (A49: at Float a NaN `x` gives NaN). Elm 0.19.1 returns 100.

The result is checked with `isNaN`, which the book defines, and then by its printed form, which
it does not (A62), though every implementation prints `NaN`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.clamp, b:Basics.isNaN
-- CHECK: clamp nan is NaN: True
-- CHECK: clamp nan: NaN

import Html exposing (text)


main =
    let
        _ =
            Debug.log "clamp nan is NaN" (isNaN (clamp -100 100 (0 / 0)))

        _ =
            Debug.log "clamp nan" (clamp -100 100 (0 / 0))
    in
    text "done"
