module TooManyArgsTooManyArgumentsToAConstructorTest exposing (..)

{-| Applying a constructor to more arguments than it takes, `Just 1 2`, is rejected with a TOO MANY ARGS error.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: TOO MANY ARGS, too many arguments to a constructor
-- CHECK: -- TOO MANY ARGS -

x = Just 1 2
