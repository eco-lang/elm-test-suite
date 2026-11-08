module TypeMismatchRigidNumberAsFunctionTest exposing (..)

{-| Returning a lambda where the annotation promises a `number` is rejected with a TYPE MISMATCH.

`f : number -> number` with `f x = \y -> y`: a function is never a `number`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-exp-lambda
-- COMPILE-ERROR: TYPE MISMATCH, rigid number as function
-- CHECK: -- TYPE MISMATCH -

f : number -> number
f x = \y -> y
