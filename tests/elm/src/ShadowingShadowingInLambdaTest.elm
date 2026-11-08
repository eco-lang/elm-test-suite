module ShadowingShadowingInLambdaTest exposing (..)

{-| A lambda argument with the same name as an argument of the enclosing function is rejected with a SHADOWING error.

In `test y = \y -> y`, the lambda's `y` shadows the function's `y`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, core-no-shadowing
-- COMPILE-ERROR: SHADOWING, shadowing in lambda
-- CHECK: -- SHADOWING -

test y =
    \y ->
        y
