module TypeMismatchUnitPatternTest exposing (..)

{-| A function annotated `Int -> Int` whose parameter is the unit pattern `()` is rejected with
a TYPE MISMATCH error.

The pattern `()` only matches the unit type, which clashes with the annotated `Int`
argument.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-atpat-unit
-- COMPILE-ERROR: TYPE MISMATCH, unit pattern
-- CHECK: -- TYPE MISMATCH -

f : Int -> Int
f () = 1
