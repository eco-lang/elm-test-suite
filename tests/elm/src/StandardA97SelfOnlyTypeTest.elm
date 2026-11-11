module StandardA97SelfOnlyTypeTest exposing (main)

{-| Matches on a type whose one constructor takes the type itself.

`type V = V V` has no finite inhabitant. A Standard Definition of Elm?, ruling A97: inhabitants may
be infinite, so `V` has the one inhabitant `V (V (V ...))`. Then `Err (V _)` covers
`Err (V (V ...))` and is not redundant in `fromResult`, and `V (V _)` covers the inhabitant of `V`
and is not redundant in `depth`. No value has type `V`, so neither branch is taken.
<https://elm-test-suite.netlify.app/standard/restrictions/core-irredundancy>
<https://elm-test-suite.netlify.app/standard/restrictions/core-exhaustiveness>

Elm 0.19.1 compiles the program. Under finite inhabitants both branches would cover nothing and
the program would be refused.

-}

-- TAGS: elm-spec, core-irredundancy, core-exhaustiveness
-- CHECK: fromResult (Ok 3): 3

import Html exposing (text)


type V
    = V V


fromResult : Result V Int -> Int
fromResult r =
    case r of
        Ok n ->
            n

        Err (V _) ->
            0


depth : V -> Int
depth v =
    case v of
        V (V _) ->
            2


main =
    let
        _ =
            Debug.log "fromResult (Ok 3)" (fromResult (Ok 3))
    in
    text "done"
