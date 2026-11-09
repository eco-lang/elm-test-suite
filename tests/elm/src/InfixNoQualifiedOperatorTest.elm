module InfixNoQualifiedOperatorTest exposing (main)

{-| `1 Basics.+ 2` is not an expression: no operator is qualified.

A Standard Definition of Elm?, Section 2.7: there are no sections, and no operator is qualified.
The grammar of expressions has no phrase for a qualified operator. <https://elm-test-suite.netlify.app/standard/figures/core-grammar-expressions>

-}

-- TAGS: elm-spec, fig:core-grammar-expressions
-- COMPILE-ERROR: a qualified operator
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH

import Html


main =
    Html.text (String.fromInt (1 Basics.+ 2))
