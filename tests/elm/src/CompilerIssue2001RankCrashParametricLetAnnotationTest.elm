module CompilerIssue2001RankCrashParametricLetAnnotationTest exposing (..)

{-| A let annotation `Dict a b` inside an unannotated function crashes the compiler.

<https://github.com/elm/compiler/issues/2001>

`dict` is `toDict value`, so its key type is fixed by the argument `value` of `fn`, while the
annotation claims it for any `a`. The annotation is too general, so a type error should be
reported; Elm 0.19.1 crashes ("You ran into a compiler bug") instead.

The issue's own program used the library type `Dict` and the function `Dict.empty`; this version
reproduces the same bug with a local two-parameter type `Dict` and its constructor `Empty` in
their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-valbind-var
-- COMPILE-ERROR: let annotation is too general
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: compiler bug

import Html


type Dict k v
    = Empty


type Foo a
    = Foo


toDict : Foo a -> Dict a b
toDict Foo =
    Empty


fn value =
    let
        dict : Dict a b
        dict =
            toDict value
    in
    ()


main =
    Html.text ""
