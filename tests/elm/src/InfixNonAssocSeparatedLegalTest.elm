module InfixNonAssocSeparatedLegalTest exposing (main)

{-| Two non-associative operators of equal precedence may share a chain when an operator of lower precedence stands between them.

A Standard Definition of Elm?, restriction core-operator-chain: two operators of equal
precedence with no operator of lower precedence between them must both associate to the left
or both to the right; otherwise the chain is not a phrase of the language. <https://elm-test-suite.netlify.app/standard/restrictions/core-operator-chain>

In `1 < 2 && 2 == 2`, `&&` (precedence 3) stands between `<` and `==` (precedence 4): the chain is
`(1 < 2) && (2 == 2)`, `True`.

-}

-- TAGS: elm-spec, core-operator-chain, fig:core-fixities, df:infix, df:and
-- CHECK: separated: True

import Html


main =
    let
        _ =
            Debug.log "separated" (1 < 2 && 2 == 2)
    in
    Html.text "done"
