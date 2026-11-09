module CompilerIssue2006IndexOutOfBoundsMaybeWithDefaultTest exposing (..)

{-| Applying a `Subtype -> Subtype` function from `withDefault` to the whole model crashes the compiler.

<https://github.com/elm/compiler/issues/2006>

`func model` passes a `Model` where a `Subtype` is expected. Elm 0.19.1 crashes ("index out of
bounds") instead of reporting the type mismatch.

The issue's own program used the library type `Dict.Dict` and the functions `Dict.get` and
`Maybe.withDefault`; this version reproduces the same bug with a local `Dict` type and local
`get` and `withDefault` of the same types in their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app
-- COMPILE-ERROR: Model is not Subtype
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: out of bounds

import Html


type Dict k v
    = Dict (List ( k, v ))


get : comparable -> Dict comparable v -> Maybe v
get key (Dict entries) =
    case entries of
        [] ->
            Nothing

        ( k, v ) :: rest ->
            if k == key then
                Just v

            else
                get key (Dict rest)


withDefault : a -> Maybe a -> a
withDefault d m =
    case m of
        Just v ->
            v

        Nothing ->
            d


type alias Subtype =
    { cog : Int }


type alias Model =
    { entry : Dict Int (Subtype -> Subtype) }


id : Subtype -> Subtype
id x =
    x


repro model key =
    let
        func =
            withDefault id (get key model.entry)
    in
    let
        x =
            func model
    in
    0


main =
    Html.text ""
