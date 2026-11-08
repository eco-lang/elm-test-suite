module BadMainTypeFunctionMainTest exposing (..)

{-| A `main` of function type `Int -> Int -> Int` is rejected with a BAD MAIN TYPE error.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, p-stat-main-program, p-stat-main-view
-- COMPILE-ERROR: BAD MAIN TYPE, function main
-- CHECK: -- BAD MAIN TYPE -

main : Int -> Int -> Int
main a b = a
