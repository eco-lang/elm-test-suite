module TopLevelPatternBindingTest exposing (main)

{-| There is no pattern binding at the top level.

A Standard Definition of Elm?, restriction modules-no-top-pattern: a top-level value declaration
binds only a variable, `x = e`. `( a, b ) = ( 1, 2 )` is a pattern binding.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-no-top-pattern>

-}

-- TAGS: elm-spec, modules-no-top-pattern
-- COMPILE-ERROR: a tuple pattern binding at the top level
-- CHECK: {{-- [A-Z ]+ -}}

import Html


( a, b ) =
    ( 1, 2 )


main =
    Html.text (String.fromInt (a + b))
