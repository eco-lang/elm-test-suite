module CompilerIssue2106FoldlExtensibleRecordHangTest exposing (main)

{-| A `foldl` whose step function extends an extensible-record type parameter must be
rejected with a type error, not hang the compiler.

<https://github.com/elm/compiler/issues/2106>

`foldl withWindow Room windows` needs `Room a` and `Room { a | withWindow : () }` to be the
same type, which would make the record type infinite. Elm 0.19.1 instead hangs while its memory
grows without bound, or crashes.

The issue's own program used the library function `List.foldl`; this version reproduces the same
bug with a local `foldl` of the same type in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app
-- COMPILE-ERROR: a type error, not a hang
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: HasCallStack

import Html


type Room a = Room

type Window = Window

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
    foldl withWindow Room windows


main =
    Html.text ""
