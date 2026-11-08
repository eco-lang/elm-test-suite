module ImportAliasQualifiedTest exposing (main)

{-| The name after `as` in an import is a single upper-case identifier.

A Standard Definition of Elm?, restriction modules-import-alias: `import Html as H.X` gives a
qualified name as the alias, so the program is rejected. <https://elm-test-suite.netlify.app/standard/restrictions/modules-import-alias>

-}

-- TAGS: elm-spec, modules-import-alias
-- COMPILE-ERROR: an import alias with a dot
-- CHECK: {{-- [A-Z ]+ -}}

import Html as H.X


main =
    H.X.text "done"
