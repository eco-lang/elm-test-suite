module TypeMismatchNumberLeftOfPipeLeftTest exposing (..)

{-| A number as the left operand of `<|` (`1 <| 2`) is rejected with a TYPE MISMATCH error, because `<|` applies its left operand as a function.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, number left of <|
-- CHECK: -- TYPE MISMATCH -

x = 1 <| 2
