module TypeExprUnitAppliedTest exposing (..)

{-| The type annotation `foo : () String Float` is rejected, and not as a TYPE MISMATCH.

<https://github.com/elm/error-message-catalog/issues/188>

The annotation places the unit type `()` before `String` and `Float` with no separator. The
test accepts any error heading except TYPE MISMATCH, which would compare the body
`( "foo", 3.2 )` against the malformed annotation.

A Standard Definition of Elm?, Figure 7 (the grammar of type expressions): a type construction
applies a type constructor to its arguments, and `()` is not a type constructor, so `() String
Float` is not a type expression; a compiler that reports a TYPE MISMATCH has read it as one.
<https://elm-test-suite.netlify.app/standard/figures/core-grammar-types>

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, fig:core-grammar-types
-- COMPILE-ERROR: a type annotation that does not parse
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: TYPE MISMATCH


foo : () String Float
foo =
    ( "foo", 3.2 )
