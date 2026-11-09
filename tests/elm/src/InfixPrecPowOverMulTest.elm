module InfixPrecPowOverMulTest exposing (main)

{-| `^` (precedence 8) binds more tightly than `*` (precedence 7).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`2 ^ 3 * 2` is `(2 ^ 3) * 2`, 16, not `2 ^ (3 * 2)`, 64.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.pow, b:Basics.mul
-- CHECK: pow then mul: 16

import Html


main =
    let
        _ =
            Debug.log "pow then mul" (2 ^ 3 * 2)
    in
    Html.text "done"
