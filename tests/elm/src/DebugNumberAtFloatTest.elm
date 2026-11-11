module DebugNumberAtFloatTest exposing (main)

{-| Unannotated functions over the `number` type that use `Debug.toString` and
`Debug.log` give the right results when called with a `Float` and with an `Int`
in the same program.

`showAll` applies `Debug.toString` to `n` and to `n + n`, and `bump` logs `n + 1`.
The test calls `showAll 1.25`, `bump 2.5` and `showAll (2 // 1)`, and checks that the
`Float` values print as `1.25`, `2.5` and `3.5` and the `Int` values as `2` and
`4`. The argument `2 // 1` is an Int; a bare `2` would be a Float, since nothing else fixes its
type (A Standard Definition of Elm?, ruling A27).

-}

-- TAGS: elm-spec, sm-topdec-value, s-atexp-scon, d-atexp-scon
-- CHECK: showAll: ["1.25","2.5"]
-- CHECK: bump: 3.5
-- CHECK: bumpResult: 3.5
-- CHECK: showAllInt: ["2","4"]

import Html exposing (text)


showAll n =
    [ Debug.toString n, Debug.toString (n + n) ]


bump n =
    Debug.log "bump" (n + 1)


main =
    let
        _ =
            Debug.log "showAll" (showAll 1.25)

        _ =
            Debug.log "bumpResult" (bump 2.5)

        _ =
            Debug.log "showAllInt" (showAll (2 // 1))
    in
    text "done"
