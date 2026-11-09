module CompilerIssue1985ImportOrderTypeAmbiguityTest exposing (..)

{-| Two imports exposing the same type name: the last one silently wins.

<https://github.com/elm/compiler/issues/1985>

`TheType` is exposed both by `CompilerIssue1985SomeTypeHelper` (`TheType a`) and by
`CompilerIssue1985MyTypeHelper` (an alias of `TheType Int`). Elm 0.19.1 picks the last import, so
this compiles and the reordered program does not. An unqualified `TheType` is ambiguous and should
be reported as such, whatever the import order.

A Standard Definition of Elm? does not accept this as a bug. The imports are read from left to
right, and a type listed by name replaces any type of that name that an earlier import provides
(rules sm-imports-import and sm-item-type): `TheType` is not ambiguous but the alias of the
second import. `Boxed 5`, of the first import's constructor, has the type `TheType Int` that the
alias stands for, so the program is valid, and Elm 0.19.1 is right to accept it.
<https://elm-test-suite.netlify.app/standard/rules/sm-item-type>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: the book has a type imported by name replace one of an earlier import, so TheType is not ambiguous and the program is valid
-- COMPILE-ERROR: ambiguous type name TheType
-- CHECK: {{-- [A-Z ]+ -}}

import CompilerIssue1985SomeTypeHelper exposing (TheType(..))
import CompilerIssue1985MyTypeHelper exposing (TheType)
import Html


type alias Model =
    { val : TheType
    }


init : Model
init =
    { val = Boxed 5 }


main =
    Html.text ""
