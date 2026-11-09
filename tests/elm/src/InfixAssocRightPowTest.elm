module InfixAssocRightPowTest exposing (main)

{-| `^` associates to the right.

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): operators of equal precedence that both associate to the left group to the
left, and both to the right, to the right. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`2 ^ 3 ^ 2` is `2 ^ (3 ^ 2)`, 512, not `(2 ^ 3) ^ 2`, 64.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.pow
-- CHECK: pow pow: 512

import Html


main =
    let
        _ =
            Debug.log "pow pow" (2 ^ 3 ^ 2)
    in
    Html.text "done"
