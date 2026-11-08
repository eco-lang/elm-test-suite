module TooManyArgsTooManyArgumentsToANullaryConstructorTest exposing (..)

{-| A constructor with no arguments applied to one is rejected with a TOO MANY ARGS error.

`T` is the only constructor of `type T = T` and takes no arguments; `x` applies it to `1`.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, s-exp-app, s-atexp-longcon, sm-conbind
-- COMPILE-ERROR: TOO MANY ARGS, too many arguments to a nullary constructor
-- CHECK: -- TOO MANY ARGS -

type T = T

x = T 1
