module InfixPrecComposeOverPipeTest exposing (main)

{-| `<<` (precedence 9) binds more tightly than `|>` (precedence 0).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

With `x = -3`, `x |> negate << abs` is `x |> (negate << abs)`, which is `negate (abs x)`, -3;
grouped as `(x |> negate) << abs` it would not type.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.composeL, b:Basics.apR
-- CHECK: compose then pipe: -3

import Html


x : Int
x =
    -3


main =
    let
        _ =
            Debug.log "compose then pipe" (x |> negate << abs)
    in
    Html.text "done"
