module StandardA44RoundNonFiniteTest exposing (main)

{-| `round`, `floor` and `ceiling` of NaN are `0`, and of an infinity an Int.

A Standard Definition of Elm?, ruling A44: they give `0` for NaN, and the greatest or least Int
for an infinity. <https://elm-test-suite.netlify.app/standard/basis/Basics/round>

Whatever the Int range, `round (1/0) - round (1/0) + 1` is then `1`. Elm 0.19.1 returns NaN or the
infinity itself, typed as an `Int`, so each line below is `False`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec
-- CHECK: round nan + 1 == 1: True
-- CHECK: floor nan + 1 == 1: True
-- CHECK: ceiling nan + 1 == 1: True
-- CHECK: round inf - round inf + 1 == 1: True
-- CHECK: floor -inf - floor -inf + 1 == 1: True
-- CHECK: ceiling inf - ceiling inf + 1 == 1: True

import Html


nan : Float
nan =
    0 / 0


inf : Float
inf =
    1 / 0


main =
    let
        _ =
            Debug.log "round nan + 1 == 1" (round nan + 1 == 1)

        _ =
            Debug.log "floor nan + 1 == 1" (floor nan + 1 == 1)

        _ =
            Debug.log "ceiling nan + 1 == 1" (ceiling nan + 1 == 1)

        _ =
            Debug.log "round inf - round inf + 1 == 1" (round inf - round inf + 1 == 1)

        _ =
            Debug.log "floor -inf - floor -inf + 1 == 1" (floor -inf - floor -inf + 1 == 1)

        _ =
            Debug.log "ceiling inf - ceiling inf + 1 == 1" (ceiling inf - ceiling inf + 1 == 1)
    in
    Html.text "done"
