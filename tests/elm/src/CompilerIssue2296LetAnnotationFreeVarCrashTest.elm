module CompilerIssue2296LetAnnotationFreeVarCrashTest exposing (main)

{-| The compiler reports a type error for a let annotation that uses a type variable belonging to an unannotated enclosing function.

<https://github.com/elm/compiler/issues/2296>

`cells : List (Node msg)` claims `cells` works for every `msg`, but it is built from `children`,
an argument of `asRow` whose `msg` is fixed by the caller. Elm 0.19.1 crashes instead ("msg [rank =
2]", Type/Solve.hs:206, "thread blocked indefinitely in an MVar operation").

The issue's own program used the library type `Html.Html` and the functions `Html.div` and
`List.map`; this version reproduces the same bug with a local `Node` type and local `div` and
`map` of the same shapes in their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-valbind-var
-- COMPILE-ERROR: a type error, not a compiler crash
-- CHECK-NOT: HasCallStack
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: bypassed the normal error reporting

import Html exposing (text)


main =
    text "done"


type Attribute msg
    = OnClick msg


type Node msg
    = Element (List (Attribute msg)) (List (Node msg))


div : List (Attribute msg) -> List (Node msg) -> Node msg
div attrs children =
    Element attrs children


map : (a -> b) -> List a -> List b
map f list =
    case list of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


asRow attrs children =
    let
        cells : List (Node msg)
        cells =
            map asCell children
    in
    div attrs cells


asCell : Node msg -> Node msg
asCell node =
    div [] [ node ]
