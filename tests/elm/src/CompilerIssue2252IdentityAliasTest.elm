module CompilerIssue2252IdentityAliasTest exposing (main)

{-| A type alias `Identity a = a` is interchangeable with `a`, so `map change = change` type-checks against `(a -> b) -> Identity a -> Identity b`.

<https://github.com/elm/compiler/issues/2252>

The annotation means `(a -> b) -> a -> b`, and `map length [ 'a', 'b', 'c' ]` should print 3.
Elm 0.19.1 rejects the definition with a TYPE MISMATCH between `a -> b` and
`Identity a -> Identity b`.

The issue's own program used the library function `String.length`; this version reproduces the
same bug with a local `length` on lists in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, sm-typbind, s-ty-con
-- CHECK: map: 3

import Html exposing (text)


type alias Identity a =
    a


map : (a -> b) -> Identity a -> Identity b
map change =
    change


length : List a -> Int
length list =
    case list of
        [] ->
            0

        _ :: rest ->
            1 + length rest


main =
    let
        _ =
            Debug.log "map" (map length [ 'a', 'b', 'c' ])
    in
    text "done"
