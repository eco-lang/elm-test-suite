module BadMainTypeUnitMainTest exposing (..)

{-| A `main` of type `()` is rejected with a BAD MAIN TYPE error.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: BAD MAIN TYPE, unit main
-- CHECK: -- BAD MAIN TYPE -

main : ()
main = ()
