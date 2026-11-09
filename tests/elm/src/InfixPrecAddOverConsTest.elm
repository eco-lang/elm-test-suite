module InfixPrecAddOverConsTest exposing (main)

{-| `+` (precedence 6) binds more tightly than `::` (precedence 5).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`1 + 1 :: [ 5 ]` is `(1 + 1) :: [ 5 ]`, `[2,5]`; grouped as `1 + (1 :: [ 5 ])` it would
not type.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.add
-- CHECK: add then cons: [2,5]

import Html


main =
    let
        _ =
            Debug.log "add then cons" (1 + 1 :: [ 5 ])
    in
    Html.text "done"
