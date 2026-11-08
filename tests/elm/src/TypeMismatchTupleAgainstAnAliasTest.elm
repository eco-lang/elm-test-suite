module TypeMismatchTupleAgainstAnAliasTest exposing (..)

{-| A list holding a value of an alias for `Int` and a tuple is rejected with a TYPE MISMATCH.

`m` has the type `N`, an alias of `Int`, and `[ m, ( 1, 2 ) ]` puts it beside a pair; list elements must all have the same type.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, sm-typbind, s-ty-con, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, tuple against an alias
-- CHECK: -- TYPE MISMATCH -

type alias N = Int

m : N
m = 1

y = [ m, ( 1, 2 ) ]
