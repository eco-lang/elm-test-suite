module TypeMismatchRigidNumberAsTupleTest exposing (..)

{-| Returning a tuple where the annotation promises a `number` is rejected with a TYPE MISMATCH.

`f : number -> number` with `f x = ( 1, 2 )`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-atexp-tuple
-- COMPILE-ERROR: TYPE MISMATCH, rigid number as tuple
-- CHECK: -- TYPE MISMATCH -

f : number -> number
f x = ( 1, 2 )
