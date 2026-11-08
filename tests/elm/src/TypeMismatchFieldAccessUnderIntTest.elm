module TypeMismatchFieldAccessUnderIntTest exposing (..)

{-| A value annotated `Int` but defined as a `String` field of a record, `r.name`, is rejected with a TYPE MISMATCH.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, field access under Int
-- CHECK: -- TYPE MISMATCH -

r = { name = "a" }

x : Int
x = r.name
