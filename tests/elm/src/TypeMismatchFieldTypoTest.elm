module TypeMismatchFieldTypoTest exposing (..)

{-| The compiler rejects access to a misspelled record field, `r.nmae` on a record whose only field is `name`, with a TYPE MISMATCH error.
-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atpat-record, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, field typo
-- CHECK: -- TYPE MISMATCH -

r = { name = "a" }

x = r.nmae
