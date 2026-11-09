module InfixNonAssocEqTwiceTest exposing (main)

{-| `a == b == c` is not a phrase: `==` associates neither way.

A Standard Definition of Elm?, restriction core-operator-chain: two operators of equal
precedence with no operator of lower precedence between them must both associate to the left
or both to the right; otherwise the chain is not a phrase of the language. <https://elm-test-suite.netlify.app/standard/restrictions/core-operator-chain>

`True == False == False` would type grouped either way; it is rejected because of the chain.

-}

-- TAGS: elm-spec, core-operator-chain, fig:core-fixities
-- COMPILE-ERROR: a non-associative operator twice in a chain
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH

import Html


main =
    Html.text (Debug.toString (True == False == False))
