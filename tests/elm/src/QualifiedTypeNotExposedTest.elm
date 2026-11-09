module QualifiedTypeNotExposedTest exposing (main)

{-| A qualified type that its module does not expose is not a type: `List.Bar` is rejected.

A Standard Definition of Elm?, rule s-ty-con: a type construction elaborates only when its long
type constructor is bound in the context; the interface of `List` binds no type constructor, so
`List.Bar` is bound to nothing. <https://elm-test-suite.netlify.app/standard/rules/s-ty-con>

-}

-- TAGS: elm-spec, s-ty-con
-- COMPILE-ERROR: a qualified type its module does not expose
-- CHECK: {{-- [A-Z ]+ -}}

import Html


foo : List.Bar
foo =
    foo


main =
    Html.text "done"
