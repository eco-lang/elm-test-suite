module StandardA1UnitPatternGapTest exposing (..)

{-| The unit pattern is `()`, with nothing between the parentheses.

A Standard Definition of Elm?, ruling A1: unit is the two characters `()` in expressions, patterns
and types alike, so `( )` is not a pattern. <https://elm-test-suite.netlify.app/standard/syntax-core#sec-syntax-core-lexical>

Elm 0.19.1 rejects `( )` as an expression or type but accepts it as a pattern.

-}

-- TAGS: elm19-bug
-- COMPILE-ERROR: a unit pattern with a gap
-- CHECK: {{-- [A-Z ]+ -}}

import Html


f : () -> Int
f ( ) =
    1


main =
    Html.text (String.fromInt (f ()))
