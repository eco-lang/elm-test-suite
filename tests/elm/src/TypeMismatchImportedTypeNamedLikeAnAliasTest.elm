module TypeMismatchImportedTypeNamedLikeAnAliasTest exposing (..)

{-| The compiler rejects a list holding both `Basics.True` and a value of a local alias named `Bool`, which stands for `Int`, with a TYPE MISMATCH error.

The local `type alias Bool = Int` shares its name with the `Bool` from `Basics`, and the two are
different types.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, sm-typbind, sm-topdec-seq, s-ty-con, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, imported type named like an alias
-- CHECK: -- TYPE MISMATCH -

type alias Bool = Int

b : Bool
b = 1

y = [ Basics.True, b ]
