module TypeMismatchFunctionLeftOfGreaterThanTest exposing (..)

{-| The compiler rejects `not > not`, comparing two functions with `>`, with a TYPE MISMATCH error, because functions are not `comparable`.
-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, function left of >
-- CHECK: -- TYPE MISMATCH -

x = not > not
