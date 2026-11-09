module TypeMismatchShaderUnderIntTest exposing (..)

{-| A GLSL shader literal annotated as `Int` is rejected with a TYPE MISMATCH.

`x : Int` is defined as `[glsl| void main () {} |]`, whose type is a `Shader`, not an `Int`.

A Standard Definition of Elm? leaves out embedded shader blocks, which belong to a graphics
extension rather than to the language (its preface): `[glsl| ... |]` is not a phrase of Standard
Elm, so the book says nothing of its type.

-}

-- TAGS: elm19-compile-error, elm-unspecced
-- COMPILE-ERROR: TYPE MISMATCH, shader under Int
-- CHECK: -- TYPE MISMATCH -

x : Int
x = [glsl| void main () {} |]
