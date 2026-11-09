module CompilerIssue1669InfiniteTypeArrayGetSetHangTest exposing (main)

{-| A function whose type would be infinite, built from `get` and `set` on a local array type in a pipeline, is rejected with a type error.

<https://github.com/elm/compiler/issues/1669>

Elm 0.19.1 hangs on it, its memory growing without bound, instead of reporting the error.

The issue's own program used the library functions `Array.get`, `Array.set`, `Maybe.map` and
`Maybe.withDefault`; this version reproduces the same bug with local definitions of the same
types in their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app
-- COMPILE-ERROR: a type error, not a hang
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: HasCallStack

import Html


type Arr a
    = Arr (List a)


get : Int -> Arr a -> Maybe a
get i (Arr xs) =
    case xs of
        [] ->
            Nothing

        x :: rest ->
            if i == 0 then
                Just x

            else
                get (i - 1) (Arr rest)


set : Int -> a -> Arr a -> Arr a
set i v (Arr xs) =
    case xs of
        [] ->
            Arr []

        x :: rest ->
            if i == 0 then
                Arr (v :: rest)

            else
                let
                    (Arr rest2) =
                        set (i - 1) v (Arr rest)
                in
                Arr (x :: rest2)


maybeMap : (a -> b) -> Maybe a -> Maybe b
maybeMap f m =
    case m of
        Just v ->
            Just (f v)

        Nothing ->
            Nothing


withDefault : a -> Maybe a -> a
withDefault d m =
    case m of
        Just v ->
            v

        Nothing ->
            d


fribble x y =
    get y x
        |> maybeMap (set y x)
        |> withDefault x


main =
    Html.text ""
