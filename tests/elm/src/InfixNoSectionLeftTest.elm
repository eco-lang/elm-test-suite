module InfixNoSectionLeftTest exposing (main)

{-| `(1 +)` is not an expression: Elm has no operator sections.

A Standard Definition of Elm?, Section 2.7: an operator value `(op)` is the only way to use an
operator other than in a chain; there are no sections. The grammar of expressions has no
phrase for one. <https://elm-test-suite.netlify.app/standard/figures/core-grammar-expressions>

-}

-- TAGS: elm-spec, fig:core-grammar-expressions
-- COMPILE-ERROR: an operator section with its left operand
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH

import Html


main =
    let
        _ =
            Debug.log "section" ((1 +) 2)
    in
    Html.text "done"
