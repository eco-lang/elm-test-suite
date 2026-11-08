module BadMainRecursiveMainTest exposing (..)

{-| An annotated `main` that is mutually recursive with another function is rejected with a BAD MAIN error.

`main : Int -> Int` calls `f`, and `f` calls `main`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, program-main, p-stat-main-program, p-stat-main-view
-- COMPILE-ERROR: BAD MAIN, recursive main
-- CHECK: -- BAD MAIN -

main : Int -> Int
main x = f x

f : Int -> Int
f x = main x
