module StandardA91BasicsAliasTest exposing (..)

{-| Only an import of the module Basics may provide the qualifier `Basics`.

A Standard Definition of Elm?, ruling A91: an import `import M as Basics` requires `M` to be
`Basics`, so that `Basics.True`, `Basics.False` and `Basics.negate`, which derived forms introduce,
always denote the initial basis. <https://elm-test-suite.netlify.app/standard/restrictions/modules-basics-qualifier>

Elm 0.19.1 accepts `import Dict as Basics`.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, modules-basics-qualifier
-- COMPILE-ERROR: import Dict as Basics
-- CHECK: {{-- [A-Z ]+ -}}

import Dict as Basics
import Html


main =
    Html.text (if 1 < 2 then "yes" else "no")
