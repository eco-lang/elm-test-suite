module TypeMismatchCharUnderIntTest exposing (..)

{-| A value annotated `Int` but defined as the character `'c'` is rejected with a TYPE MISMATCH.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, char under Int
-- CHECK: -- TYPE MISMATCH -

x : Int
x = 'c'
