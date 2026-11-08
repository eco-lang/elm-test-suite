module BadTupleATupleOfFourTest exposing (..)

{-| A four-element tuple is rejected with a BAD TUPLE error.

Elm tuples have at most three elements; `testValue` is `( 1, 2, 3, 4 )`.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: BAD TUPLE, a tuple of four
-- CHECK: -- BAD TUPLE -

testValue =
    ( 1, 2, 3, 4 )
