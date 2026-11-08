module BadMainTypeFunctionMainTest exposing (..)

{-| A `main` of function type `Int -> Int -> Int` is rejected with a BAD MAIN TYPE error.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: BAD MAIN TYPE, function main
-- CHECK: -- BAD MAIN TYPE -

main : Int -> Int -> Int
main a b = a
