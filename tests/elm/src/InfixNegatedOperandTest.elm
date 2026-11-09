module InfixNegatedOperandTest exposing (main)

{-| A negation symbol in an operator chain negates the atomic expression after it, and no more.

A Standard Definition of Elm?, Section 2.7: each operand of a chain may be negated; and Section 2.5,
the negation symbol negates the atomic expression after it, and no more.
<https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`-2 ^ 2` is `(-2) ^ 2`, 4, not `-(2 ^ 2)`, -4; and `3 - -2` is `3 - (-2)`, 5.

-}

-- TAGS: elm-spec, fig:core-fixities, core-adjacent-items, df:negation, df:infix, b:Basics.pow, b:Basics.sub
-- CHECK: negated pow: 4
-- CHECK: sub negated: 5

import Html


main =
    let
        _ =
            Debug.log "negated pow" (-2 ^ 2)

        _ =
            Debug.log "sub negated" (3 - -2)
    in
    Html.text "done"
