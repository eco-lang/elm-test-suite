module TypeMismatchFunctionLeftOfGreaterThanTest exposing (..)

{-| The compiler rejects `not > not`, comparing two functions with `>`, with a TYPE MISMATCH error, because functions are not `comparable`.
-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, function left of >
-- CHECK: -- TYPE MISMATCH -

x = not > not
