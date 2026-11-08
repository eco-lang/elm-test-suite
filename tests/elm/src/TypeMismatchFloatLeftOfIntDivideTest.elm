module TypeMismatchFloatLeftOfIntDivideTest exposing (..)

{-| The compiler rejects the `Float` literal `1.5` on the left of the integer division operator `//`, with a TYPE MISMATCH error.
-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app, s-atexp-scon
-- COMPILE-ERROR: TYPE MISMATCH, Float left of //
-- CHECK: -- TYPE MISMATCH -

x = 1.5 // 2
