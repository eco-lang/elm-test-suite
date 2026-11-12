module StandardA98TypeBeforeAliasStringMismatchTest exposing (main)

{-| A custom type declared before a local alias spelt like an imported type uses the local alias.

The module declares `type T = T String` and then `type alias String = Int`, and applies
`String.length` to the field of a `T`. A Standard Definition of Elm?, ruling A98: the module's type
declarations are elaborated together, so `T`'s argument is the local `String`, which is `Int`, and
`String.length` cannot take it. Reading the declarations in order would make the argument the
imported `String`, and the program would be accepted.
<https://elm-test-suite.netlify.app/standard/rules/sm-topdec-types>

Elm 0.19.1, 0.19.2 and 0.19.3 reject the program with TYPE MISMATCH.

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, sm-topdec-types, sm-topdec-seq, sm-datbind
-- COMPILE-ERROR: TYPE MISMATCH, the field of T is the local String
-- CHECK: -- TYPE MISMATCH -

import Html exposing (text)


type T
    = T String


type alias String =
    Int


len : T -> Int
len (T s) =
    String.length s


main =
    text (Debug.toString (len (T 3)))
