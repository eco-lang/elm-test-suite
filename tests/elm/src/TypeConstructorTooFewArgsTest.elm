module TypeConstructorTooFewArgsTest exposing (main)

{-| A type constructor given fewer arguments than it takes is not a type: `List -> List` is
rejected.

A Standard Definition of Elm?, rule s-ty-con: a type construction `T t1 ... tk` elaborates only
when `T` takes exactly k arguments, and `List` takes one. <https://elm-test-suite.netlify.app/standard/rules/s-ty-con>

-}

-- TAGS: elm-spec, s-ty-con
-- COMPILE-ERROR: List without its argument
-- CHECK: {{-- [A-Z ]+ -}}

import Html


foo : List -> List
foo xs =
    xs


main =
    Html.text "done"
