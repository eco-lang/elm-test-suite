module CompilerIssue2097ExtensibleUnitArgCrashTest exposing (main, f)

{-| An extensible-record alias applied to `()` must be rejected with an error report, not crash
the compiler.

<https://github.com/elm/compiler/issues/2097>

Elm 0.19.1 crashes with "Used toAnnotation on a type that is not well-formed" (Type/Type.hs) and
"thread blocked indefinitely in an MVar operation". `()` is not a record, so the program must be
rejected with an ordinary error report.

The issue's own program used the library function `List.map` in `f`; this version reproduces the
same bug with a local `map` of the same type in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-ty-con
-- COMPILE-ERROR: an ordinary error report, not a compiler crash
-- CHECK-NOT: HasCallStack
-- CHECK-NOT: not well-formed
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: bypassed the normal error reporting

import Html exposing (text)


main =
    text "done"


type alias Extensible comparable a =
    { a | id : comparable }


type alias T =
    Extensible String ()


map : (a -> b) -> List a -> List b
map g list =
    case list of
        [] ->
            []

        x :: rest ->
            g x :: map g rest


f : List T -> List String
f list =
    map .id list
