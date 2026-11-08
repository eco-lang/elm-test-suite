module StandardA51FunctionEqualityTest exposing (main)

{-| `==` on two functions gives a Bool; the program goes on.

<https://github.com/elm/compiler/issues/1145>

A Standard Definition of Elm?, ruling A51: equality that reaches two functions gives a Bool that
the definition does not specify; no evaluation ends in a run-time error.
<https://elm-test-suite.netlify.app/standard/basis/Basics/eq>

Elm 0.19.1 stops the program: "Trying to use `(==)` on functions."

-}

-- TAGS: elm19-bug
-- CHECK: compared: True

import Html


main =
    let
        -- Two different functions: Elm 0.19.1 first checks whether both operands are one
        -- object, so `identity == identity` would not reach the functions.
        same =
            (\k -> k + 1) == (\k -> k + 2)

        _ =
            Debug.log "compared" (same || not same)
    in
    Html.text "done"
