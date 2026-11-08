module TypeMismatchUnitLeftOfAtLeastTest exposing (..)

{-| Comparing two unit values with `>=` is rejected with a TYPE MISMATCH error.

`>=` takes `comparable` arguments, and `()` is not comparable.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, unit left of >=
-- CHECK: -- TYPE MISMATCH -

x = () >= ()
