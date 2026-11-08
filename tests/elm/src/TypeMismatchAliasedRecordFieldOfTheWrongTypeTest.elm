module TypeMismatchAliasedRecordFieldOfTheWrongTypeTest exposing (..)

{-| A record whose field has the wrong type for its record alias annotation is rejected with a TYPE MISMATCH.

`x` is annotated `P`, an alias of `{ a : Int }`, but its field `a` is the string `"s"`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-ty-con, s-atexp-record
-- COMPILE-ERROR: TYPE MISMATCH, aliased record field of the wrong type
-- CHECK: -- TYPE MISMATCH -

type alias P = { a : Int }

x : P
x = { a = "s" }
