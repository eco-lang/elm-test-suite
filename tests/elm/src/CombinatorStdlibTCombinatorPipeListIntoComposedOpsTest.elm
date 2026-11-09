module CombinatorStdlibTCombinatorPipeListIntoComposedOpsTest exposing (..)

{-| The T combinator, built from S and K inside a `let`, passing `[ 1, 2, 3 ]` to the composition of a sum and a doubling map: the result is 12.

Every combinator is a local definition in `testValue`: `b = s (k s) k`,
`c = s (b b s) (k k)`, `i = s k k` and `t = c i`. The composed function is
`b mySum mapDouble`, where `mySum` and `mapDouble` are local recursive
functions defined by pattern matching on the list, so `t [ 1, 2, 3 ] composed` is `mySum (mapDouble [ 1, 2, 3 ])`.

-}

-- TAGS: elm-spec, s-atexp-let, s-dec-group, d-app-closure
-- CHECK: testValue: 12

import Basics exposing (..)
import Html


testValue =
    let
        k a _ =
            a

        s bf uf x =
            bf x (uf x)

        b =
            s (k s) k

        c =
            s (b b s) (k k)

        i =
            s k k

        t =
            c i

        mySum xs =
            case xs of
                [] ->
                    0

                a :: rest ->
                    a + mySum rest

        mapDouble xs =
            case xs of
                [] ->
                    []

                x :: rest ->
                    x * 2 :: mapDouble rest

        composed =
            b mySum mapDouble
    in
    t [ 1, 2, 3 ] composed


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    Html.text "done"
