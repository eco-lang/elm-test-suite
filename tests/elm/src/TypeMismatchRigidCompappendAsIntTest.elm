module TypeMismatchRigidCompappendAsIntTest exposing (..)

{-| Returning an annotated `compappend` value where the annotation says `Int` is rejected with a TYPE MISMATCH.

`f : compappend -> Int` with `f x = x`: the caller chooses the `compappend` type, so it cannot be assumed to be `Int`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var
-- COMPILE-ERROR: TYPE MISMATCH, rigid compappend as Int
-- CHECK: -- TYPE MISMATCH -

f : compappend -> Int
f x = x
