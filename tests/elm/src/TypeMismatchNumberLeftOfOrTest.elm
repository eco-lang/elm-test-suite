module TypeMismatchNumberLeftOfOrTest exposing (..)

{-| A number as the left operand of `||` (`1 || True`) is rejected with a TYPE MISMATCH error, because `||` takes two `Bool`s.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-exp-case, s-atpat-con, s-atexp-scon
-- COMPILE-ERROR: TYPE MISMATCH, number left of ||
-- CHECK: -- TYPE MISMATCH -

x = 1 || True
