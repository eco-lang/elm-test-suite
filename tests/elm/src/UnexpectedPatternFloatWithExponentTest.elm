module UnexpectedPatternFloatWithExponentTest exposing (main)

{-| A case branch whose pattern is the float literal `1e3` is rejected with an UNEXPECTED
PATTERN error.

Elm patterns may match integer, character and string literals but not floats, and a literal
written with an exponent is a float.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, core-no-float-pattern
-- COMPILE-ERROR: UNEXPECTED PATTERN
-- CHECK: -- UNEXPECTED PATTERN -


f x =
    case x of
        1e3 ->
            1

        _ ->
            2


main =
    f 2
