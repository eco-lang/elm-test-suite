module TypeMismatchRigidVarAsFunctionTest exposing (..)

{-| Returning a lambda where the annotation promises a type variable `a` is rejected with a TYPE MISMATCH.

`f : a -> a` with `f x = \y -> y`: the caller chooses `a`, so it cannot be fixed to a function type.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TYPE MISMATCH, rigid var as function
-- CHECK: -- TYPE MISMATCH -

f : a -> a
f x = \y -> y
