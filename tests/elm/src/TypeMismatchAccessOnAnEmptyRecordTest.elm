module TypeMismatchAccessOnAnEmptyRecordTest exposing (..)

{-| Reading a field from an empty record is rejected with a TYPE MISMATCH.

`r` is `{}`, which has no fields, and `x = r.foo` reads a field `foo` from it.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, access on an empty record
-- CHECK: -- TYPE MISMATCH -

r = {}

x = r.foo
