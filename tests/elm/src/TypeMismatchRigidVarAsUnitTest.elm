module TypeMismatchRigidVarAsUnitTest exposing (..)

{-| A function annotated `a -> a` that returns unit is rejected with a TYPE MISMATCH.

`f x = ()` returns `()`, but the annotation promises the type variable `a`, which the body may not specialise.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-atexp-unit
-- COMPILE-ERROR: TYPE MISMATCH, rigid var as unit
-- CHECK: -- TYPE MISMATCH -

f : a -> a
f x = ()
