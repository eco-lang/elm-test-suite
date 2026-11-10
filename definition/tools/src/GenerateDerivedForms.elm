module GenerateDerivedForms exposing (run)

{-| Writes the derived forms of Appendix A from `DerivedForms.Table`: the six `derivedforms` tables
of `definition/tex/appendix-derived-forms.tex` and the derived-form functions of
`definition/mechanisation/standard-elm-mech/StandardElmMech/Derived.lean`. Each goes between marker
lines; the rest of each file is left as it is. Run from the repository's root:

    site/node_modules/.bin/elm-pages run definition/tools/src/GenerateDerivedForms.elm

-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import DerivedForms.Table as Table
import DerivedForms.Term exposing (Block(..), Row, blockName)
import DerivedForms.ToLatex as ToLatex
import DerivedForms.ToLean as ToLean
import Dict
import FatalError exposing (FatalError)
import Pages.Script as Script exposing (Script)
import Regions


texPath : String
texPath =
    "definition/tex/appendix-derived-forms.tex"


leanPath : String
leanPath =
    "definition/mechanisation/standard-elm-mech/StandardElmMech/Derived.lean"


blocks : List Block
blocks =
    [ Expressions, AtomicExpressions, AtomicPatterns, ValueBindings, Declarations, TopLevelDeclarations ]


{-| The new text of the appendix: each block's region replaced by its table.
-}
latex : String -> Result String String
latex source =
    let
        rows =
            Dict.fromList (List.map (\r -> ( r.label, r )) Table.rows)

        step b acc =
            acc
                |> Result.andThen
                    (Regions.replace
                        { begin = "% BEGIN GENERATED derived-forms:" ++ blockName b ++ " "
                        , end = "% END GENERATED derived-forms:" ++ blockName b
                        }
                        (ToLatex.block rows (List.filter (\r -> r.block == b) Table.rows))
                    )
    in
    List.foldl step (Ok source) blocks


lean : String -> Result String String
lean source =
    ToLean.definitions Table.rows
        |> Result.andThen
            (\defs ->
                Regions.replace
                    { begin = "-- BEGIN GENERATED derived forms"
                    , end = "-- END GENERATED derived forms"
                    }
                    defs
                    source
            )


write : String -> (String -> Result String String) -> BackendTask FatalError ()
write path transform =
    BackendTask.File.rawFile path
        |> BackendTask.allowFatal
        |> BackendTask.andThen
            (\source ->
                case transform source of
                    Ok text ->
                        if text == source then
                            Script.log (path ++ ": unchanged")

                        else
                            Script.writeFile { path = path, body = text }
                                |> BackendTask.allowFatal
                                |> BackendTask.andThen (\_ -> Script.log (path ++ ": written"))

                    Err problem ->
                        BackendTask.fail (FatalError.fromString (path ++ ": " ++ problem))
            )


run : Script
run =
    Script.withoutCliOptions
        (write texPath latex
            |> BackendTask.andThen (\_ -> write leanPath lean)
        )
