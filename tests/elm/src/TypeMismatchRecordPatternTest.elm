module TypeMismatchRecordPatternTest exposing (..)

{-| A record pattern on an argument annotated as `Int` is rejected with a TYPE MISMATCH.

`f : Int -> Int` with `f { a } = a`: the pattern `{ a }` needs a record, but the annotation says the argument is an `Int`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-atpat-record
-- COMPILE-ERROR: TYPE MISMATCH, record pattern
-- CHECK: -- TYPE MISMATCH -

f : Int -> Int
f { a } = a
