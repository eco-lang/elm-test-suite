module CompilerIssue1822AliasOfRecordAliasConstructorTest exposing (..)

{-| An alias of a record type alias has no record constructor.

<https://github.com/elm/compiler/issues/1822>

`Y` is an alias of the record alias `X`, so `Y` should construct an `X` like `X` does. Elm 0.19.1
reports "I cannot find a `Y` variant".

A Standard Definition of Elm? does not accept this as a bug. Only a record alias, an alias whose
type is a record type expression, declares a constructor of its name (restriction
modules-constructors-distinct). `type alias Y = X` aliases an alias, not a record type, so `Y` is
no constructor, and the program, which uses it as one, is rejected.
<https://elm-test-suite.netlify.app/standard/restrictions/modules-constructors-distinct>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: the book gives a constructor only to an alias of a record type, so Y is no constructor and the program is rejected
-- CHECK: y: { a = "a", b = "b" }

import Html exposing (text)


type alias X =
    { a : String, b : String }


type alias Y =
    X


main =
    let
        _ =
            Debug.log "y" (Y "a" "b")
    in
    text "done"
