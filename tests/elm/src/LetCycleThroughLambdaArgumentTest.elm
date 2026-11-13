module LetCycleThroughLambdaArgumentTest exposing (main)

{-| A `let` definition without parameters that lies on a cycle is rejected, even when the cycle
goes through a lambda: here a lambda passed as an argument to `Result.andThen`.

`broken = Err () |> Result.andThen (\_ -> ... broken ...)` refers to itself, and is not a function
binding with parameters. The lambda is never called, since `Result.andThen` does not call it on an
`Err`, but the program is rejected all the same.

A Standard Definition of Elm?, restriction core-let-recursion: every definition of a `let` that
lies on a cycle of the refers-to relation is a function binding with at least one parameter; no
definition `var = exp` without parameters lies on a cycle, even when `exp` is a lambda
expression. <https://elm-test-suite.netlify.app/standard/restrictions/core-let-recursion>

-}

-- TAGS: elm-spec, core-let-recursion
-- COMPILE-ERROR: a let value on a cycle through a lambda argument
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: Crash

import Html


main =
    let
        broken : Result () ()
        broken =
            Err ()
                |> Result.andThen
                    (\_ ->
                        if False then
                            broken

                        else
                            Ok ()
                    )
    in
    Html.text ""
