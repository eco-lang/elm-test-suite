module InfixMixedAssocPipesTest exposing (main)

{-| `a |> f <| b` is not a phrase: `|>` and `<|` have equal precedence and associate in opposite ways.

A Standard Definition of Elm?, restriction core-operator-chain: two operators of equal
precedence with no operator of lower precedence between them must both associate to the left
or both to the right; otherwise the chain is not a phrase of the language. <https://elm-test-suite.netlify.app/standard/restrictions/core-operator-chain>

`1 |> (+) <| 2` would type grouped either way, and give 3 either way.

-}

-- TAGS: elm-spec, core-operator-chain, fig:core-fixities
-- COMPILE-ERROR: a left and a right associative operator of equal precedence
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH

import Html


main =
    let
        _ =
            Debug.log "piped" (1 |> (+) <| 2)
    in
    Html.text "done"
