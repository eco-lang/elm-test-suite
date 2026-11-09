module InfixLastOperandAnyExprTest exposing (main)

{-| The last operand of a chain may be any expression: an `if` or a lambda.

A Standard Definition of Elm?, Section 2.7: each operand of an operator chain is an application or an
atomic expression, possibly negated, except that the last operand may be any expression.
<https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`1 + if True then 2 else 3` is 3, and `5 |> \n -> n * 2` is 10.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, df:if, d-exp-lambda
-- CHECK: if last: 3
-- CHECK: lambda last: 10

import Html


main =
    let
        _ =
            Debug.log "if last" (1 + if True then 2 else 3)

        _ =
            Debug.log "lambda last" (5 |> \n -> n * 2)
    in
    Html.text "done"
