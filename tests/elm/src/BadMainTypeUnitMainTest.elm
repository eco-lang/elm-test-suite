module BadMainTypeUnitMainTest exposing (..)

{-| A `main` of type `()` is rejected with a BAD MAIN TYPE error.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, p-stat-main-program, p-stat-main-view
-- COMPILE-ERROR: BAD MAIN TYPE, unit main
-- CHECK: -- BAD MAIN TYPE -

main : ()
main = ()
