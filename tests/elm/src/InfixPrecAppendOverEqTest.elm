module InfixPrecAppendOverEqTest exposing (main)

{-| `++` (precedence 5) binds more tightly than `==` (precedence 4).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`[ 1 ] ++ [ 2 ] == [ 1, 2 ]` is `([ 1 ] ++ [ 2 ]) == [ 1, 2 ]`, `True`; grouped as
`[ 1 ] ++ ([ 2 ] == [ 1, 2 ])` it would not type.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.append, b:Basics.eq
-- CHECK: append then eq: True

import Html


main =
    let
        _ =
            Debug.log "append then eq" ([ 1 ] ++ [ 2 ] == [ 1, 2 ])
    in
    Html.text "done"
