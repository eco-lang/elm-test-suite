module StandardA96NumberFlagsTest exposing (main)

{-| A `main` whose flags type is a `number` variable is refused.

`init = \n -> ( n + 1, Cmd.none )` and nothing else fixes the type of the flags, so in the
principal type of `main` they are a type variable of class `number`. A Standard Definition of Elm?,
ruling A96: rule p-stat-main-program checks that the flags type is a port type in the principal
scheme of `main`, before the default of `number` to Float, and a type variable is not a port type.
<https://elm-test-suite.netlify.app/standard/rules/p-stat-main-program>

Elm 0.19.1 refuses the program with BAD FLAGS: "type variables like `number` cannot be given as
flags".

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, p-stat-main-program
-- COMPILE-ERROR: BAD FLAGS, flags of class number
-- CHECK: -- BAD FLAGS -


main =
    Platform.worker
        { init = \n -> ( n + 1, Cmd.none )
        , update = \_ m -> ( m, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
