module TypeMismatchDestructureTest exposing (..)

{-| Destructuring the number `1` with the tuple pattern `( a, b )` in a `let` is rejected with a TYPE MISMATCH.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, destructure
-- CHECK: -- TYPE MISMATCH -

x =
    let
        ( a, b ) = 1
    in
    a
