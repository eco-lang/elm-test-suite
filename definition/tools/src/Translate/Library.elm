module Translate.Library exposing
    ( Library
    , Text
    , closure
    , copied
    , empty
    , fromSchemes
    , member
    , scheme
    , textSource
    , used
    )

{-| The core library values the translator evaluates (plans/library-elm-texts.md, decisions L1 to
L3): the values of `List`, `Maybe`, `Result` and `Tuple` that elm/core 1.0.5 defines by Elm text,
each with the type scheme its annotation in the vendored file elaborates to.

A test program refers to them as to values of the basis (`Global m x`, `Exposed m x`); the dynamic
test basis binds them (`Lib.Btest` in Lean), to the values Chapter 7's rules give their texts, which
the translator writes as modules (`Generated/Library.lean`). A text's module is the vendored file
with only the declarations of the closure kept (`closure`) and its imports of `Elm.Kernel.*` left
out (`textSource`); the one kernel value the texts may name is `Elm.Kernel.List.cons`, the list
constructor, which the converter writes `(::)`.

-}

import Dict exposing (Dict)
import Elm.Syntax.Declaration exposing (Declaration(..))
import Elm.Syntax.File exposing (File)
import Elm.Syntax.Node as Node exposing (Node(..))
import Set exposing (Set)
import Translate.Classify as Classify
import Translate.Ir exposing (Decl(..), Expr(..), Name(..), TestProgram, anyExpr)
import Translate.Types exposing (Class(..), Scheme)


{-| The library: each value by its module and name, with its scheme (variables negative, as the
basis's are, `Translate.Basis`).
-}
type alias Library =
    { schemes : Dict ( String, String ) Scheme }


empty : Library
empty =
    { schemes = Dict.empty }


fromSchemes : List ( ( String, String ), Scheme ) -> Library
fromSchemes entries =
    { schemes = Dict.fromList entries }


member : Library -> String -> String -> Bool
member lib m x =
    Dict.member ( m, x ) lib.schemes


scheme : Library -> String -> String -> Maybe Scheme
scheme lib m x =
    Dict.get ( m, x ) lib.schemes


{-| The variables of class number that a library value's scheme quantifies, in its order; [] for a
value without copies. The texts with such a scheme are specialised as a program's code is (L3):
their default copy is at Float, and the module binds a copy for every other assignment.
-}
copied : Library -> String -> String -> List Int
copied lib m x =
    scheme lib m x
        |> Maybe.map (.quantified >> List.filter (\( _, c ) -> c == Number) >> List.map Tuple.first)
        |> Maybe.withDefault []


{-| A library module to translate: its name, its vendored file, the values the translator evaluates.
-}
type alias Text =
    { modul : String, path : String, values : List String }


{-| The top-level values of a module that the given values need: the values, and every top-level
value their texts name unqualified, transitively, in the order the file declares them. A name a text
binds locally is taken as naming the top-level value of that name too, if there is one; that can
only keep a declaration that is not needed.
-}
closure : File -> List String -> List String
closure file values =
    let
        functions =
            file.declarations
                |> List.filterMap
                    (\(Node _ d) ->
                        case d of
                            FunctionDeclaration f ->
                                Just ( Node.value (Node.value f.declaration).name, f )

                            _ ->
                                Nothing
                    )

        byName =
            Dict.fromList functions

        refsOf x =
            case Dict.get x byName of
                Just f ->
                    (Classify.functionRefs f Classify.emptyRefs).unqualified
                        |> List.filter (\y -> Dict.member y byName)

                Nothing ->
                    []

        go queue seen =
            case queue of
                [] ->
                    seen

                x :: rest ->
                    if Set.member x seen then
                        go rest seen

                    else
                        go (rest ++ refsOf x) (Set.insert x seen)

        needed =
            go values Set.empty
    in
    functions |> List.map Tuple.first |> List.filter (\x -> Set.member x needed)


{-| The file a library module is translated from: the vendored file with the declarations of the
closure only (no custom type: a module's constructors are ME0's already, by the default imports)
and without its imports of `Elm.Kernel.*`. The texts themselves are not changed.
-}
textSource : File -> List String -> File
textSource file values =
    let
        keep =
            Set.fromList (closure file values)
    in
    { file
        | declarations =
            file.declarations
                |> List.filter
                    (\(Node _ d) ->
                        case d of
                            FunctionDeclaration f ->
                                Set.member (Node.value (Node.value f.declaration).name) keep

                            _ ->
                                False
                    )
        , imports =
            file.imports
                |> List.filter (\(Node _ i) -> List.take 2 (Node.value i.moduleName) /= [ "Elm", "Kernel" ])
    }


{-| The library values a converted program names, as `M.x`, sorted.
-}
used : Library -> TestProgram -> List String
used lib program =
    let
        names e =
            case e of
                EVar _ (Global m x) ->
                    if member lib m x then
                        [ m ++ "." ++ x ]

                    else
                        []

                EVar _ (Exposed m x) ->
                    if member lib m x then
                        [ m ++ "." ++ x ]

                    else
                        []

                _ ->
                    []

        collect e =
            if anyExpr (\x -> not (List.isEmpty (names x))) e then
                names e ++ List.concatMap collect (Translate.Ir.children e)

            else
                []
    in
    program.modules
        |> List.concatMap .defs
        |> List.concatMap
            (\d ->
                case d of
                    DFn f ->
                        collect f.body

                    DPat _ x ->
                        collect x
            )
        |> Set.fromList
        |> Set.toList
