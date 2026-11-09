module InfixPrecApplicationFirstTest exposing (main)

{-| Application binds more tightly than any operator.

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`negate 2 ^ 2` is `(negate 2) ^ 2`, 4, not `negate (2 ^ 2)`, -4; and `(+) 1 2 * 3` is
`((+) 1 2) * 3`, 9, not `(+) 1 (2 * 3)`, 7.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, d-exp-app, d-atexp-op, b:Basics.negate, b:Basics.pow, b:Basics.add
-- CHECK: application then pow: 4
-- CHECK: application then mul: 9

import Html


main =
    let
        _ =
            Debug.log "application then pow" (negate 2 ^ 2)

        _ =
            Debug.log "application then mul" ((+) 1 2 * 3)
    in
    Html.text "done"
