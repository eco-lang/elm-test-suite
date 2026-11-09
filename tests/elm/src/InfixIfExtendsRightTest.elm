module InfixIfExtendsRightTest exposing (main)

{-| An `if` extends as far right as it can: its `else` branch takes in a chain after it.

A Standard Definition of Elm?, Section 2.9: `if` (like a lambda, `case` and `let`) extends as far
right as the layout rule allows, and is written in parentheses when it is an operand of a chain
other than the last. <https://elm-test-suite.netlify.app/standard/figures/core-grammar-expressions>

`if True then 10 else 2 * 3` is `if True then 10 else (2 * 3)`, 10, not
`(if True then 10 else 2) * 3`, 30.

-}

-- TAGS: elm-spec, fig:core-grammar-expressions, df:if, df:infix
-- CHECK: if then chain: 10

import Html


main =
    let
        _ =
            Debug.log "if then chain" (if True then 10 else 2 * 3)
    in
    Html.text "done"
