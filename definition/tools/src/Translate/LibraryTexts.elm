module Translate.LibraryTexts exposing (build)

{-| The core library values the translator evaluates, from the texts of their vendored files
(plans/library-elm-texts.md, step 1): the library the tests may name, each value with the scheme of
its annotation (`Infer.librarySchemes`), and the text of `Generated/Library.lean` after its header:
one module per library module, the closure of its values' texts (`Library.closure`), converted,
inferred and specialised by the translator's own pipeline, exposing the values and their copies
(`sum` and `sum$Int`). A text that names a kernel value other than `Elm.Kernel.List.cons` is
refused, and so the whole library (`Err`).
-}

import Elm.Parser
import Elm.Syntax.Declaration as Declaration
import Elm.Syntax.Node as Node
import Translate.Convert as Convert
import Translate.Infer as Infer
import Translate.Ir as Ir
import Translate.Library as Library exposing (Library)
import Translate.Specialise as Specialise
import Translate.ToLean as ToLean


build : List ( Library.Text, String ) -> Result String { library : Library, lean : String }
build texts =
    let
        parsed =
            texts
                |> List.map
                    (\( t, src ) ->
                        Elm.Parser.parseToFile src
                            |> Result.mapError (\_ -> t.path ++ ": does not parse")
                            |> Result.map (\file -> ( t, src, file ))
                    )
                |> List.foldr (Result.map2 (::)) (Ok [])

        annotationsOf ( t, _, file ) =
            t.values
                |> List.map
                    (\x ->
                        file.declarations
                            |> List.filterMap
                                (\(Node.Node _ d) ->
                                    case d of
                                        Declaration.FunctionDeclaration f ->
                                            if Node.value (Node.value f.declaration).name == x then
                                                f.signature |> Maybe.map (\(Node.Node _ sig) -> ( ( t.modul, x ), sig.typeAnnotation ))

                                            else
                                                Nothing

                                        _ ->
                                            Nothing
                                )
                            |> List.head
                            |> Result.fromMaybe (t.path ++ ": " ++ x ++ " has no annotation")
                    )

        exposingOf t m =
            case m.exposes of
                Ir.ExposeItems items ->
                    Ir.ExposeItems (List.filter (\item -> List.member item (List.map Ir.IVar t.values)) items)

                Ir.ExposeAll ->
                    Ir.ExposeItems (List.map Ir.IVar t.values)
    in
    parsed
        |> Result.andThen
            (\files ->
                files
                    |> List.concatMap annotationsOf
                    |> List.foldr (Result.map2 (::)) (Ok [])
                    |> Result.andThen Infer.librarySchemes
                    |> Result.map (\schemes -> ( files, Library.fromSchemes schemes ))
            )
        |> Result.andThen
            (\( files, lib ) ->
                let
                    sources =
                        List.map (\( t, src, file ) -> { name = t.modul, path = t.path, source = src, file = Library.textSource file t.values }) files

                    ( modules0, problems ) =
                        Convert.convertLibrary sources

                    modules =
                        List.map2 (\( t, _, _ ) m -> { m | exposes = exposingOf t m }) files modules0
                in
                case problems of
                    p :: _ ->
                        Err (p.code ++ " at " ++ String.fromInt p.at.start.row ++ ":" ++ String.fromInt p.at.start.column)

                    [] ->
                        Infer.inferLibrary modules
                            |> Result.andThen (Specialise.specialiseLibrary modules)
                            |> Result.map (\specialised -> { library = lib, lean = leanText specialised })
            )


leanText : List Ir.ModuleIr -> String
leanText modules =
    let
        defName m =
            "libText_" ++ String.replace "." "_" m.name
    in
    "import StandardElmMech.Examples\n\nnamespace StandardElm\nopen StandardElm.D\n\n"
        ++ String.join "\n\n" (List.map (\m -> ToLean.libraryDef (defName m) m) modules)
        ++ "\n\n/-- The library modules the dynamic test basis evaluates (plans/library-elm-texts.md), in order:\n    the texts of elm/core 1.0.5 that the values the tests name need. -/\ndef libTexts : List ModSrc :=\n  ["
        ++ String.join ", " (List.map defName modules)
        ++ "]\n\nend StandardElm\n"
