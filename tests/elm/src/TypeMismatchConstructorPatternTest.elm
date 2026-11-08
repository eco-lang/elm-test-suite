module TypeMismatchConstructorPatternTest exposing (..)

{-| A `case` on the number `1` with a `Just a` branch is rejected with a TYPE MISMATCH, because the pattern is a `Maybe` and the value is a number.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-exp-case, s-pat-con, s-atexp-scon
-- COMPILE-ERROR: TYPE MISMATCH, constructor pattern
-- CHECK: -- TYPE MISMATCH -

x =
    case 1 of
        Just a ->
            1

        _ ->
            2
