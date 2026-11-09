module CompilerIssue1979ImportOpaqueConstructorsTest exposing (..)

{-| Importing `Opaque(..)` from a module that exposes `Opaque` without its constructors is accepted.

<https://github.com/elm/compiler/issues/1979>

`CompilerIssue1979OpaqueHelper` exposes only `Opaque`, but Elm 0.19.1 accepts
`exposing (Opaque(..))` without complaint. Exposing constructors that the module does not expose
should be an import error.

A Standard Definition of Elm? does not accept this as a bug. For a type that its module exposes
without its constructors, `import A exposing (T(..))` elaborates, imports the type and imports
no constructor (the comment on rule sm-item-opentype). The program uses no constructor of
`Opaque`, so it is valid, and Elm 0.19.1 is right to accept it.
<https://elm-test-suite.netlify.app/standard/rules/sm-item-opentype>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: the book accepts T(..) of a type exposed without constructors, importing none, so the program is valid
-- COMPILE-ERROR: the imported module does not expose Opaque's constructors
-- CHECK: {{-- [A-Z ]+ -}}

import CompilerIssue1979OpaqueHelper exposing (Opaque(..))
import Html


a : Opaque
a =
    CompilerIssue1979OpaqueHelper.make


main =
    Html.text ""
