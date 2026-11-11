module StandardA97NeverErrBranchTest exposing (main)

{-| A branch for the error of a `Result Never a` is not redundant.

`Never` has one constructor, `JustOneMore`, which takes a `Never`, so `Never` has no finite
inhabitant. A Standard Definition of Elm?, ruling A97: inhabitants may be infinite, so `Never` has
the inhabitant `JustOneMore (JustOneMore ...)`, the branch `Err e -> never e` covers
`Err (JustOneMore ...)`, and the match is irredundant. No value has type `Never`, so the branch is
never taken. <https://elm-test-suite.netlify.app/standard/restrictions/core-irredundancy>

Elm 0.19.1 compiles the program. Under finite inhabitants the branch would cover nothing and the
program would be refused.

-}

-- TAGS: elm-spec, core-irredundancy
-- CHECK: value (Ok 3): 3

import Html exposing (text)


value : Result Never Int -> Int
value r =
    case r of
        Ok n ->
            n

        Err e ->
            never e


main =
    let
        _ =
            Debug.log "value (Ok 3)" (value (Ok 3))
    in
    text "done"
