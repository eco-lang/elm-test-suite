module CompilerIssue2182ExtensibleFunctionAliasCrashTest exposing (main)

{-| An alias that extends its parameter with a field the parameter already has is not a type.

<https://github.com/elm/compiler/issues/2182>

With `type alias Goal a = { a | field : Int } -> a`, Elm 0.19.1 accepts
`solution : Goal { field : Int }` / `solution = identity`, the outer `field` winning, but crashes
with "Map.!: given key is not an element in the map" on `puzzle rec = rec`, which is the same
function.

A Standard Definition of Elm?, ruling A23: a record row has unique labels, and a row variable
ranges only over rows that lack the labels already present. `Goal { field : Int }` would give the
record a second `field`, so the substitution is not defined, the alias cannot be applied, and
neither annotation elaborates. The program must be refused, with no crash.
<https://elm-test-suite.netlify.app/standard/static-core#sec-static-core-types>

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-ty-con, sm-typbind, sec:static-core-types
-- COMPILE-ERROR: a row extended with a label it already has
-- CHECK: {{-- [A-Z ]+ -}}

import Html exposing (text)


type alias Goal a =
    { a | field : Int } -> a


solution : Goal { field : Int }
solution =
    identity


puzzle : Goal { field : Int }
puzzle rec =
    rec


main =
    let
        _ =
            ( solution, puzzle )
    in
    text "done"
