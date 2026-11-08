module ImportClosedTypeConstructorTest exposing (main)

{-| A custom type exposed without `(..)` exposes no constructor, even one spelt as the type.

A Standard Definition of Elm?, rules sm-item-type and dm-expitem-type: `ModuleExposingHelper`
exposes `Shape` closed, so `import ModuleExposingHelper exposing (Shape)` imports the type
`Shape` and not its constructor `Shape`. <https://elm-test-suite.netlify.app/standard/rules/dm-expitem-type>

-}

-- TAGS: elm-spec, sm-item-type, dm-expitem-type
-- COMPILE-ERROR: a use of a constructor of a type exposed closed
-- CHECK: {{-- [A-Z ]+ -}}

import Html
import ModuleExposingHelper exposing (Shape)


main =
    Html.text (String.fromInt (ModuleExposingHelper.unwrapShape (Shape 1)))
