module StandardA56PrefixAndOrTest exposing (main)

{-| `(&&)` and `(||)` used as functions evaluate both arguments, like every other function.

A Standard Definition of Elm?, ruling A56: only the infix forms `a && b` and `a || b` are
conditionals (derived forms); the operator values `(&&)` and `(||)` are functions of the basis,
applied to two values. <https://elm-test-suite.netlify.app/standard/basis/Basics/and>

Elm 0.19.1 compiles `(&&) a b` and `(||) a b` like the infix forms, so the second argument is
evaluated only when needed and its `Debug.log` never runs.

-}

-- TAGS: elm19-bug
-- CHECK: second argument of (&&): True
-- CHECK: (&&) False _: False
-- CHECK: second argument of (||): False
-- CHECK: (||) True _: True

import Html


main =
    let
        _ =
            Debug.log "(&&) False _" ((&&) False (Debug.log "second argument of (&&)" True))

        _ =
            Debug.log "(||) True _" ((||) True (Debug.log "second argument of (||)" False))
    in
    Html.text "done"
