module TypeMismatchRecordWhereEmptyClosedRecordTest exposing (..)

{-| A record with a field, given where the annotation says the empty record `{}`, is rejected with a TYPE MISMATCH.

`x : {}` with `x = { a = 1 }`: `{}` is a closed record type with no fields, so the extra field `a` does not fit.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, record where empty closed record
-- CHECK: -- TYPE MISMATCH -

x : {}
x = { a = 1 }
