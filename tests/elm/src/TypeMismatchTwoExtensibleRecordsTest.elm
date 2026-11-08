module TypeMismatchTwoExtensibleRecordsTest exposing (..)

{-| An extensible record returned where the annotation promises a record with a different extension variable is rejected with a TYPE MISMATCH.

`g : { r | name : Int } -> { s | name : Int }` returns its argument unchanged. `r` and `s` are separate type variables chosen by the caller, so a record extending `r` is not a record extending `s`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-ty-openrecord
-- COMPILE-ERROR: TYPE MISMATCH, two extensible records
-- CHECK: -- TYPE MISMATCH -

g : { r | name : Int } -> { s | name : Int }
g r = r
