module CompilerIssue2105ExtensibleFoldlCrashTest exposing (main, withWindows)

{-| Folding with a function that extends a record type parameter must produce a complete type
error report, not crash the compiler.

<https://github.com/elm/compiler/issues/2105>

`foldl withWindow room windows` needs `Room a` and `Room { a | withWindow : () }` to be the
same type, which they are not. Elm 0.19.1 starts printing the TYPE MISMATCH report, then crashes
with "Used toErrorType on a type that is not well-formed" (Type/Type.hs:541).

The issue's own program used the library function `List.foldl`; this version reproduces the same
bug with a local `foldl` of the same type in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app, s-valbind-var
-- COMPILE-ERROR: a type error, not a compiler crash
-- CHECK-NOT: HasCallStack
-- CHECK-NOT: not well-formed
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: bypassed the normal error reporting

import Html exposing (text)


main =
    text "done"


type Room a
    = Room


type Window
    = Window


foldl : (a -> b -> b) -> b -> List a -> b
foldl f acc list =
    case list of
        [] ->
            acc

        x :: rest ->
            foldl f (f x acc) rest


withWindow : Window -> Room a -> Room { a | withWindow : () }
withWindow window room =
    Room


withWindows : List Window -> Room a -> Room { a | withWindow : () }
withWindows windows room =
    foldl withWindow room windows
