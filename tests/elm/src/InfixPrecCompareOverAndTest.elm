module InfixPrecCompareOverAndTest exposing (main)

{-| `<` (precedence 4) binds more tightly than `&&` (precedence 3).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`1 < 2 && 3 < 4` is `(1 < 2) && (3 < 4)`, `True`; grouped any other way it would not type.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, df:and, b:Basics.lt
-- CHECK: lt then and: True

import Html


main =
    let
        _ =
            Debug.log "lt then and" (1 < 2 && 3 < 4)
    in
    Html.text "done"
