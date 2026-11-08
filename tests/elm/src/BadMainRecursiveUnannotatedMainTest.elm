module BadMainRecursiveUnannotatedMainTest exposing (..)

{-| An unannotated `main` that is mutually recursive with another function is rejected with a BAD MAIN error.

`main x` calls `f x`, and `f x` calls `main x`; neither has a type annotation.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, program-main, p-stat-main-program, p-stat-main-view
-- COMPILE-ERROR: BAD MAIN, recursive unannotated main
-- CHECK: -- BAD MAIN -

main x = f x

f x = main x
