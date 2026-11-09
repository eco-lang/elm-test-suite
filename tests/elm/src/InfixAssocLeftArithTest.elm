module InfixAssocLeftArithTest exposing (main)

{-| `-`, `/` and `//` associate to the left.

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): operators of equal precedence that both associate to the left group to the
left, and both to the right, to the right. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`10 - 3 - 2` is `(10 - 3) - 2`, 5, not 9; `100 / 10 / 2` is 5, not 20; `100 // 10 // 3` is
3, not 100.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.sub, b:Basics.fdiv, b:Basics.idiv
-- CHECK: sub sub: 5
-- CHECK: fdiv fdiv: 5
-- CHECK: idiv idiv: 3

import Html


main =
    let
        _ =
            Debug.log "sub sub" (10 - 3 - 2)

        _ =
            Debug.log "fdiv fdiv" (100 / 10 / 2)

        _ =
            Debug.log "idiv idiv" (100 // 10 // 3)
    in
    Html.text "done"
