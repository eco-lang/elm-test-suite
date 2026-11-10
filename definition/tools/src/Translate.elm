module Translate exposing (run)

{-| Translates the `elm-spec` tests of `tests/` into Lean for the mechanisation of A Standard
Definition of Elm? (plans/elm-to-lean-translator.md). Run from the repository's root:

    site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm            -- write
    site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check    -- compare only

It writes, under `definition/mechanisation/standard-elm-mech/StandardElmMech/Generated/`, one Lean
file of programs per shard (at most 40 tests), `All.lean`, and one file of theorems per shard; the
list of those modules in `StandardElmMech.lean`; and `definition/mechanisation/translation-manifest.json`,
with every `elm-spec` test, translated or refused with its reason. With `--check` it writes nothing:
it prints the files that would change, and exits 0 either way.

-}

import BackendTask exposing (BackendTask)
import BackendTask.Custom
import BackendTask.File
import BackendTask.Glob as Glob
import Cli.Option as Option
import Cli.OptionsParser as OptionsParser
import Cli.Program as Program
import Dict
import FatalError exposing (FatalError)
import Json.Decode as Decode
import Json.Encode as Encode
import Pages.Script as Script exposing (Script)
import Regions
import Translate.Directives as Directives
import Translate.Pipeline as Pipeline exposing (Outcome(..))


mech : String
mech =
    "definition/mechanisation/standard-elm-mech/"


generatedDir : String
generatedDir =
    mech ++ "StandardElmMech/Generated/"


manifestPath : String
manifestPath =
    "definition/mechanisation/translation-manifest.json"


shardSize : Int
shardSize =
    40


type alias Test =
    { project : String, name : String, path : String }


type alias Entry =
    { test : Test, sha : String, outcome : Outcome, defName : String }


config : Program.Config Bool
config =
    Program.config
        |> Program.add
            (OptionsParser.build identity
                |> OptionsParser.with (Option.flag "check")
            )


tests : BackendTask FatalError (List Test)
tests =
    Glob.succeed (\project name -> { project = project, name = name, path = "tests/" ++ project ++ "/src/" ++ name ++ ".elm" })
        |> Glob.match (Glob.literal "tests/")
        |> Glob.capture Glob.wildcard
        |> Glob.match (Glob.literal "/src/")
        |> Glob.capture Glob.wildcard
        |> Glob.match (Glob.literal ".elm")
        |> Glob.toBackendTask
        |> BackendTask.map (List.sortBy (\t -> ( t.project, t.name )))


sha256 : String -> BackendTask FatalError String
sha256 path =
    BackendTask.Custom.run "sha256File" (Encode.string path) Decode.string |> BackendTask.allowFatal


upperCamel : String -> String
upperCamel project =
    String.split "-" project
        |> List.map (\w -> String.toUpper (String.left 1 w) ++ String.dropLeft 1 w)
        |> String.concat


defNameOf : Test -> String
defNameOf t =
    "g_" ++ String.replace "-" "_" t.project ++ "_" ++ t.name


entry : Test -> BackendTask FatalError (Maybe Entry)
entry t =
    BackendTask.File.rawFile t.path
        |> BackendTask.allowFatal
        |> BackendTask.andThen
            (\source ->
                let
                    directives =
                        Directives.read source
                in
                if List.member "elm-spec" directives.tags && not directives.helper then
                    sha256 t.path
                        |> BackendTask.map
                            (\sha ->
                                Just
                                    { test = t
                                    , sha = sha
                                    , outcome = Pipeline.translate { project = t.project, name = t.name, defName = defNameOf t } source directives
                                    , defName = defNameOf t
                                    }
                            )

                else
                    BackendTask.succeed Nothing
            )


type alias Shard =
    { name : String, entries : List ( Entry, String ) }


shards : List Entry -> List Shard
shards entries =
    let
        translated =
            List.filterMap
                (\e ->
                    case e.outcome of
                        Translated t ->
                            Just ( e, t.lean )

                        Refused _ ->
                            Nothing
                )
                entries

        projects =
            translated |> List.map (\( e, _ ) -> e.test.project) |> unique
    in
    projects
        |> List.concatMap
            (\project ->
                translated
                    |> List.filter (\( e, _ ) -> e.test.project == project)
                    |> chunks shardSize
                    |> List.indexedMap
                        (\i chunk ->
                            { name = upperCamel project ++ String.padLeft 2 '0' (String.fromInt (i + 1)), entries = chunk }
                        )
            )


unique : List comparable -> List comparable
unique =
    List.foldl
        (\x acc ->
            if List.member x acc then
                acc

            else
                acc ++ [ x ]
        )
        []


chunks : Int -> List a -> List (List a)
chunks n xs =
    if List.isEmpty xs then
        []

    else
        List.take n xs :: chunks n (List.drop n xs)


header : String
header =
    "/- Generated by definition/tools/src/Translate.elm from the tests in tests/. Do not edit. -/\n"


shardFile : Shard -> String
shardFile shard =
    header
        ++ "import StandardElmMech.Examples\n\nnamespace StandardElm\nopen StandardElm.D\n\n"
        ++ String.join "\n\n" (List.map Tuple.second shard.entries)
        ++ "\n\n/-- The programs of this shard. -/\ndef shard_"
        ++ shard.name
        ++ " : List Program :=\n  ["
        ++ String.join ",\n   " (List.map (\( e, _ ) -> e.defName) shard.entries)
        ++ "]\n\nend StandardElm\n"


allFile : List Shard -> String
allFile all =
    header
        ++ String.concat (List.map (\s -> "import StandardElmMech.Generated." ++ s.name ++ "\n") all)
        ++ "\nnamespace StandardElm\n\n/-- Every shard of generated programs, by name. -/\ndef generatedShards : List (String × List Program) :=\n  ["
        ++ String.join ",\n   " (List.map (\s -> "(\"" ++ s.name ++ "\", shard_" ++ s.name ++ ")") all)
        ++ "]\n\n/-- Every generated program. -/\ndef generatedPrograms : List Program :=\n  generatedShards.foldr (fun s acc => s.2 ++ acc) []\n\nend StandardElm\n"


checksFile : Shard -> String
checksFile shard =
    header
        ++ "import StandardElmMech.Generated."
        ++ shard.name
        ++ "\nimport StandardElmMech.Theorems\n\nnamespace StandardElm\nopen StandardElm.D\n\n#kernel_checks shard_"
        ++ shard.name
        ++ " \""
        ++ shard.name
        ++ "\"\n\n/-- Every check of this shard that expects a value, and is not a known divergence, is\n    derivable by the rules with the value its test expects. -/\ntheorem derivable_"
        ++ shard.name
        ++ " : ∀ p ∈ shard_"
        ++ shard.name
        ++ ", ∀ ck ∈ p.checks, ck.expected ≠ \"(no value)\" →\n    ¬ knownDiv.contains (p.name, ck.label) = true →\n      ∃ v, EvalExp p.env (p.phrase ck) v ∧ showElm v = ck.expected :=\n  derivableOf shard_"
        ++ shard.name
        ++ " (by native_decide)\n\nend StandardElm\n"


rootRegion : List Shard -> String
rootRegion all =
    String.join "\n"
        ("import StandardElmMech.Generated.All"
            :: List.map (\s -> "import StandardElmMech.Generated.Checks" ++ s.name) all
        )


manifest : String -> List Entry -> String
manifest toolsSha entries =
    let
        encodeEntry e shardOf =
            Encode.object
                ([ ( "project", Encode.string e.test.project )
                 , ( "name", Encode.string e.test.name )
                 , ( "sha256", Encode.string e.sha )
                 ]
                    ++ (case e.outcome of
                            Translated t ->
                                [ ( "status", Encode.string "translated" )
                                , ( "shard", Encode.string (Maybe.withDefault "" shardOf) )
                                , ( "def", Encode.string e.defName )
                                , ( "checks", Encode.int t.checks )
                                , ( "lean", Encode.string t.lean )
                                ]

                            Refused r ->
                                [ ( "status", Encode.string "refused" )
                                , ( "reason", Encode.string r.reason )
                                ]
                                    ++ (r.at |> Maybe.map (\a -> [ ( "at", Encode.string a ) ]) |> Maybe.withDefault [])
                                    ++ (r.detail |> Maybe.map (\d -> [ ( "detail", Encode.string d ) ]) |> Maybe.withDefault [])
                       )
                )

        shardIndex =
            shards entries
                |> List.concatMap (\s -> List.map (\( e, _ ) -> ( e.defName, s.name )) s.entries)
                |> Dict.fromList
    in
    Encode.encode 2
        (Encode.object
            [ ( "generatedBy", Encode.string "definition/tools/src/Translate.elm" )
            , ( "toolsSha256", Encode.string toolsSha )
            , ( "tests", Encode.list (\e -> encodeEntry e (Dict.get e.defName shardIndex)) entries )
            ]
        )
        ++ "\n"


type alias Output =
    { path : String, body : String }


{-| Every file the translator writes, with its new text. The root module's text is the old one
with its region replaced.
-}
outputs : String -> List Entry -> String -> Result String (List Output)
outputs toolsSha entries rootSource =
    let
        all =
            shards entries
    in
    Regions.replace { begin = "-- BEGIN GENERATED translations", end = "-- END GENERATED translations" } (rootRegion all) rootSource
        |> Result.map
            (\root ->
                List.map (\s -> { path = generatedDir ++ s.name ++ ".lean", body = shardFile s }) all
                    ++ List.map (\s -> { path = generatedDir ++ "Checks" ++ s.name ++ ".lean", body = checksFile s }) all
                    ++ [ { path = generatedDir ++ "All.lean", body = allFile all }
                       , { path = mech ++ "StandardElmMech.lean", body = root }
                       , { path = manifestPath, body = manifest toolsSha entries }
                       ]
            )


summary : List Entry -> String
summary entries =
    let
        reasons =
            entries
                |> List.filterMap
                    (\e ->
                        case e.outcome of
                            Refused r ->
                                Just (reasonClass r.reason)

                            Translated _ ->
                                Nothing
                    )

        counts =
            List.foldl (\r d -> Dict.update r (\c -> Just (Maybe.withDefault 0 c + 1)) d) Dict.empty reasons

        translated =
            List.length entries - List.length reasons
    in
    "elm-spec tests: "
        ++ String.fromInt (List.length entries)
        ++ ", translated: "
        ++ String.fromInt translated
        ++ "\n"
        ++ String.join "\n" (List.map (\( r, c ) -> "  " ++ String.padLeft 4 ' ' (String.fromInt c) ++ "  " ++ r) (List.reverse (List.sortBy Tuple.second (Dict.toList counts))))


{-| A refusal reason without its detail, for counting: `basis:String.fromInt` counts as
`basis:String.fromInt`, `checks:unmatched:x` as `checks:unmatched`.
-}
reasonClass : String -> String
reasonClass reason =
    if String.startsWith "checks:unmatched:" reason then
        "checks:unmatched"

    else
        reason


run : Script
run =
    Script.withCliOptions config
        (\check ->
            tests
                |> BackendTask.andThen (\ts -> BackendTask.sequence (List.map entry ts))
                |> BackendTask.map (List.filterMap identity)
                |> BackendTask.andThen
                    (\entries ->
                        BackendTask.map2 Tuple.pair
                            (BackendTask.File.rawFile (mech ++ "StandardElmMech.lean") |> BackendTask.allowFatal)
                            (BackendTask.Custom.run "sha256Tree" (Encode.string "definition/tools/src") Decode.string |> BackendTask.allowFatal)
                            |> BackendTask.andThen
                                (\( rootSource, toolsSha ) ->
                                    case outputs toolsSha entries rootSource of
                                        Err problem ->
                                            BackendTask.fail (FatalError.fromString ("StandardElmMech.lean: " ++ problem))

                                        Ok files ->
                                            Script.log (summary entries)
                                                |> BackendTask.andThen
                                                    (\_ ->
                                                        if check then
                                                            compareAll files

                                                        else
                                                            writeAll files
                                                    )
                                )
                    )
        )


writeAll : List Output -> BackendTask FatalError ()
writeAll files =
    Script.makeDirectory { recursive = True } generatedDir
        |> BackendTask.andThen
            (\_ ->
                files
                    |> List.map (\f -> Script.writeFile f |> BackendTask.allowFatal)
                    |> BackendTask.sequence
                    |> BackendTask.andThen (\_ -> Script.log ("written: " ++ String.fromInt (List.length files) ++ " files"))
            )


compareAll : List Output -> BackendTask FatalError ()
compareAll files =
    files
        |> List.map
            (\f ->
                BackendTask.File.rawFile f.path
                    |> BackendTask.toResult
                    |> BackendTask.map
                        (\r ->
                            case r of
                                Ok old ->
                                    if old == f.body then
                                        Nothing

                                    else
                                        Just ("would change: " ++ f.path)

                                Err _ ->
                                    Just ("would create: " ++ f.path)
                        )
            )
        |> BackendTask.combine
        |> BackendTask.andThen
            (\changes ->
                case List.filterMap identity changes of
                    [] ->
                        Script.log "Lean translations are up to date."

                    cs ->
                        Script.log (String.join "\n" cs ++ "\n" ++ String.fromInt (List.length cs) ++ " file(s) differ from what the translator would write; run it, then the mechanisation stage.")
            )
