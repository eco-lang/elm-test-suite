module TypeMismatchRigidExtensionWhereClosedTest exposing (..)

{-| Returning an extensible record argument where the annotation says a closed record is rejected with a TYPE MISMATCH.

`g : { r | name : Int } -> { name : Int }` with `g r = r`: the argument may carry fields beyond `name`, which the closed result type `{ name : Int }` does not allow.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-valbind-var, s-ty-openrecord
-- COMPILE-ERROR: TYPE MISMATCH, rigid extension where closed
-- CHECK: -- TYPE MISMATCH -

g : { r | name : Int } -> { name : Int }
g r = r
