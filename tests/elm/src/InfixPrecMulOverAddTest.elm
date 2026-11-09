module InfixPrecMulOverAddTest exposing (main)

{-| `*` (precedence 7) binds more tightly than `+` (precedence 6).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`2 + 3 * 4` is `2 + (3 * 4)`, 14, not 20; `2 * 3 + 4` is `(2 * 3) + 4`, 10, not 14.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.add, b:Basics.mul
-- CHECK: add then mul: 14
-- CHECK: mul then add: 10

import Html


main =
    let
        _ =
            Debug.log "add then mul" (2 + 3 * 4)

        _ =
            Debug.log "mul then add" (2 * 3 + 4)
    in
    Html.text "done"
