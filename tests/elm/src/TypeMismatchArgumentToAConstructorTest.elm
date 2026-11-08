module TypeMismatchArgumentToAConstructorTest exposing (..)

{-| A constructor applied to an argument of the wrong type is rejected with a TYPE MISMATCH.

`T` wraps an `Int`, and `x = T "s"` gives it a `String`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-exp-app, s-atexp-longcon, sm-conbind
-- COMPILE-ERROR: TYPE MISMATCH, argument to a constructor
-- CHECK: -- TYPE MISMATCH -

type T = T Int

x = T "s"
