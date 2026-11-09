module InfixNonAssocCompareTest exposing (main)

{-| `a < b == c` is not a phrase: `<` and `==` have equal precedence and associate neither way.

A Standard Definition of Elm?, restriction core-operator-chain: two operators of equal
precedence with no operator of lower precedence between them must both associate to the left
or both to the right; otherwise the chain is not a phrase of the language. <https://elm-test-suite.netlify.app/standard/restrictions/core-operator-chain>

The book's example. The error must be the chain's, not a type error.

-}

-- TAGS: elm-spec, core-operator-chain, fig:core-fixities
-- COMPILE-ERROR: two non-associative operators of equal precedence
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH

import Html


main =
    Html.text (Debug.toString (1 < 2 == True))
