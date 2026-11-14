module Compiler.Core.Name exposing
    ( Name
    , fromPtr
    , mainModule
    )

{-| Every identifier the compiler handles is a `Name`.

A `Name` is the text of an identifier: a value, type, constructor, record
field, type variable or module, spelled as in source or as the compiler makes
it up. A module name keeps its dots, as in `Elm.Kernel.List`.

(Vendored from eco-compiler; see `VENDORED.md`. Only the names the vendored
parser uses are kept.)


# Core Type

@docs Name


# Construction

@docs fromPtr


# Names of Modules

@docs mainModule

-}



-- ====== NAME ======


{-| The text of an identifier, spelled as in source or as the compiler makes it
up.

This is a name for `String`, not a new type. Any `String` is accepted where a
`Name` is expected, so the compiler cannot tell a value name from a module
name, or a qualified name from a bare one.

-}
type alias Name =
    String



-- ====== FROM ======


{-| Returns the part of `src` from index `start` up to, but not including, index
`end`, counted as `String.slice` counts them.
-}
fromPtr : String -> Int -> Int -> Name
fromPtr src start end =
    String.slice start end src



-- ====== CONSTANTS ======


{-| The name `Main`, given to a module whose source has no `module` line.
-}
mainModule : Name
mainModule =
    "Main"
