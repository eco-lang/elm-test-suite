module TypeMismatchBoolsComparedTest exposing (..)

{-| `True < False` is rejected with a TYPE MISMATCH, because `<` takes comparable values and `Bool` is not comparable.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-atexp-op, s-exp-app
-- COMPILE-ERROR: TYPE MISMATCH, Bools compared
-- CHECK: -- TYPE MISMATCH -

x = True < False
