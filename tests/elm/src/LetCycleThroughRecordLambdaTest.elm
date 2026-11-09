module LetCycleThroughRecordLambdaTest exposing (main)

{-| A `let` definition without parameters that lies on a cycle is rejected, even when the cycle
goes through a lambda: here a record whose field is a lambda that refers back to the record.

`func = { f = \n -> ... func.f ... }` refers to itself, and is not a function binding with
parameters.

A Standard Definition of Elm?, restriction core-let-recursion: every definition of a `let` that
lies on a cycle of the refers-to relation is a function binding with at least one parameter; no
definition `var = exp` without parameters lies on a cycle, even when `exp` is a lambda
expression. <https://elm-test-suite.netlify.app/standard/restrictions/core-let-recursion>

-}

-- TAGS: elm-spec, core-let-recursion
-- COMPILE-ERROR: a let value on a cycle through a lambda
-- CHECK: {{-- [A-Z ]+ -}}

import Html


factorial : Int -> Int
factorial num =
    let
        eval f x =
            f () x

        func =
            { f =
                \n ->
                    if n == 0 then
                        1

                    else
                        n * eval (\_ -> func.f) (n - 1)
            }
    in
    func.f num


main =
    let
        _ =
            Debug.log "factorial" (factorial 5)
    in
    Html.text "done"
