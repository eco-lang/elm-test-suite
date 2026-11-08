module TypeMismatchIntRightOfAppendTest exposing (..)

{-| The compiler rejects `"a" ++ n`, appending an `Int` to a `String`, with a TYPE MISMATCH error.
-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, Int right of ++
-- CHECK: -- TYPE MISMATCH -

n : Int
n = 1

x = "a" ++ n
