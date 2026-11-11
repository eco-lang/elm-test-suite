module StandardA97MaybeNeverMissingJustTest exposing (main)

{-| A `case` on a `Maybe Never` must have a branch for `Just`.

A Standard Definition of Elm?, ruling A97: inhabitants may be infinite, so `Maybe Never` has the
inhabitant `Just (JustOneMore (JustOneMore ...))`, which `Nothing` does not cover, and the match is
not exhaustive. <https://elm-test-suite.netlify.app/standard/restrictions/core-exhaustiveness>

Elm 0.19.1 rejects the program with MISSING PATTERNS. Under finite inhabitants `Nothing` would be
the only inhabitant, and the program would be accepted.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, core-exhaustiveness
-- COMPILE-ERROR: MISSING PATTERNS, Just on a Maybe Never
-- CHECK: -- MISSING PATTERNS -

import Html exposing (text)


count : Maybe Never -> Int
count m =
    case m of
        Nothing ->
            0


main =
    let
        _ =
            Debug.log "count Nothing" (count Nothing)
    in
    text "done"
