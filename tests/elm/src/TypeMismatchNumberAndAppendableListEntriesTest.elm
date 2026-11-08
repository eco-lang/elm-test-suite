module TypeMismatchNumberAndAppendableListEntriesTest exposing (..)

{-| A list literal whose entries are `a + 1` and `b ++ b` is rejected with a TYPE MISMATCH error.

All entries of a list share one type. The first entry must be a `number` and the second an `appendable`, and no type is both.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, number and appendable list entries
-- CHECK: -- TYPE MISMATCH -

f a b = [ a + 1, b ++ b ]
