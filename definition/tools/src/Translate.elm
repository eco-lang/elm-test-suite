module Translate exposing (run)

{-| Translates the `elm-spec` tests of `tests/` into Lean for the mechanisation of A Standard
Definition of Elm? (plans/elm-to-lean-translator.md). Run from the repository's root:

    node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm

    node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check

    node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --report-all-refusals FILE

eco's parser recurses deeply: node's default stack is too small for some tests, hence the flag
(plans/eco-parser.md, E12).

It writes, under `definition/mechanisation/standard-elm-mech/StandardElmMech/Generated/`, one Lean
file of programs per shard (a fixed alphabetical bucket of test names, `bucketOf`), `All.lean`, and
one file of theorems per shard, and removes any file there it wrote before but no longer writes; the
list of those modules in `StandardElmMech.lean`; and `definition/mechanisation/translation-manifest.json`,
with every `elm-spec` test, translated or refused with its reason. With `--check` it writes nothing:
it prints the files that would change, and exits 0 either way. With `--report-all-refusals FILE` it
writes only FILE: for every `elm-spec` test, every refusal met when each is lifted in turn (step 0
of plans/lean-full-definition.md).

-}

import BackendTask exposing (BackendTask)
import BackendTask.Custom
import BackendTask.File
import BackendTask.Glob as Glob
import Cli.Option as Option
import Cli.OptionsParser as OptionsParser
import Cli.Program as Program
import Dict exposing (Dict)
import FatalError exposing (FatalError)
import Json.Decode as Decode
import Json.Encode as Encode
import Pages.Script as Script exposing (Script)
import Regions
import Set exposing (Set)
import StaticBasis.Json as SB
import Translate.Choices as Choices exposing (Choices)
import Translate.Classify as Classify
import Translate.ClassifyOverrides as ClassifyOverrides
import Translate.Convert as Convert
import Translate.Directives as Directives
import Translate.FrontEnd as FrontEnd
import Translate.Library as Library exposing (Library)
import Translate.LibraryTexts as LibraryTexts
import Translate.Parse as Parse
import Translate.Pipeline as Pipeline exposing (Outcome(..))
import Translate.Region as Region
import Translate.Source as Source


mech : String
mech =
    "definition/mechanisation/standard-elm-mech/"


generatedDir : String
generatedDir =
    mech ++ "StandardElmMech/Generated/"


manifestPath : String
manifestPath =
    "definition/mechanisation/translation-manifest.json"


{-| The shards are fixed alphabetical buckets of the key `project/Test` (`bucketOf`), so that adding,
removing or renaming a test changes its own bucket's files only, and Lake rebuilds only what imports
them. A bucket's files are named after its bound (`bucketName`: `elm/CaseF` gives `Elm_CaseF`,
`elm/` gives `Elm`). A bucket that grows too large is split by adding a bound, which changes that
bucket's files and adds one.

The buckets of the translated view programs (`Elm_*.lean` and `ChecksElm_*.lean`). They are the
bounds of the end-to-end certificates (`e2eBounds` in Certify.lean), so that each certificate file
imports the program and check files of its own bucket only; if the two lists differ, nothing is
wrong but a change spreads to more files.

-}
viewBounds : List String
viewBounds =
    [ "elm-core/"
    , "elm-core/CompareI"
    , "elm-core/CoreIssue115"
    , "elm-core/FloatD"
    , "elm-core/FloatSu"
    , "elm-core/NotEqualBoolP"
    , "elm-core/StandardA42"
    , "elm-core/TaskOnErrorS"
    , "elm/"
    , "elm/Ap"
    , "elm/As"
    , "elm/CaseF"
    , "elm/CaseS"
    , "elm/CharU"
    , "elm/CombinatorL"
    , "elm/CombinatorP"
    , "elm/CombinatorSP"
    , "elm/CompilerIssue22"
    , "elm/CovTailRecPairParameters"
    , "elm/EmbeddedNo"
    , "elm/Fli"
    , "elm/ImportE"
    , "elm/InfixPrecO"
    , "elm/LetN"
    , "elm/LetNumberLo"
    , "elm/Li"
    , "elm/M"
    , "elm/PartialAppCh"
    , "elm/PortEchoN"
    , "elm/RecordAccessorFunctionT"
    , "elm/SingleCtorPairBoolF"
    , "elm/StandardL"
    , "elm/TailRecT"
    ]


{-| The buckets of the source programs (`SrcElm_*.lean`, and one `SynElm_*.lean` each), chosen on
2026-11-13 as every 40th of the 918 written programs.
-}
srcBounds : List String
srcBounds =
    [ "elm-core/"
    , "elm-core/CoreIssue112"
    , "elm-core/FloatS"
    , "elm-core/StandardA41"
    , "elm/"
    , "elm/CaseCustomTypeT"
    , "elm/CharC"
    , "elm/CompilerIssue176"
    , "elm/CompilerIssue217"
    , "elm/CustomTypeUnboundV"
    , "elm/Flo"
    , "elm/InfixAssocP"
    , "elm/LetNumberAp"
    , "elm/LetNumberRecordM"
    , "elm/Mu"
    , "elm/PolyStepLoopFo"
    , "elm/RecordNarrow06"
    , "elm/StandardA9"
    , "elm/TooManyArgsTooManyArgumentsToAN"
    , "elm/TypeMismatchCon"
    , "elm/TypeMismatchListE"
    , "elm/TypeMismatchRigidNumberAsF"
    , "elm/TypeMismatchTu"
    , "elm/WideRecordDecoder30T"
    ]


{-| The bucket of a key: the last bound (in the order of `String`) that is not after it, or the first
bound. The same as `bucketOf` in Certify.lean.
-}
bucketOf : List String -> String -> String
bucketOf bounds key =
    let
        sorted =
            List.sort bounds
    in
    sorted
        |> List.filter (\b -> b <= key)
        |> List.reverse
        |> List.head
        |> Maybe.withDefault (List.head sorted |> Maybe.withDefault "")


{-| The name of a bucket's files: `elm/CaseF` gives `Elm_CaseF`, `elm-core/` gives `ElmCore`.
-}
bucketName : String -> String
bucketName bound =
    case String.split "/" bound of
        [ project, prefix ] ->
            upperCamel project
                ++ (if prefix == "" then
                        ""

                    else
                        "_" ++ prefix
                   )

        _ ->
            "All"


{-| The items in their buckets, in the order of the bounds, each bucket's items in their given order;
empty buckets are left out.
-}
bucketed : List String -> (a -> String) -> List a -> List ( String, List a )
bucketed bounds keyOf xs =
    let
        tagged =
            List.map (\x -> ( bucketOf bounds (keyOf x), x )) xs
    in
    List.sort bounds
        |> List.filterMap
            (\b ->
                case
                    List.filterMap
                        (\( c, x ) ->
                            if c == b then
                                Just x

                            else
                                Nothing
                        )
                        tagged
                of
                    [] ->
                        Nothing

                    ys ->
                        Just ( b, ys )
            )


type alias Test =
    { project : String, name : String, path : String }


type alias Entry =
    { test : Test, sha : String, outcome : Outcome, defName : String, source : String, sources : List { path : String, sha : String } }


{-| Every source of every project, by project and module name, so that a test's imports of its
project's modules can be read (plan step 3).
-}
type alias Sources =
    Dict String (Dict String { path : String, source : String })


readSources : List Test -> BackendTask FatalError Sources
readSources ts =
    ts
        |> List.map
            (\t ->
                BackendTask.File.rawFile t.path
                    |> BackendTask.allowFatal
                    |> BackendTask.map (\src -> ( t, src ))
            )
        |> BackendTask.sequence
        |> BackendTask.map
            (List.foldl
                (\( t, src ) d ->
                    Dict.update t.project
                        (\m -> Just (Dict.insert t.name { path = t.path, source = src } (Maybe.withDefault Dict.empty m)))
                        d
                )
                Dict.empty
            )


lookupIn : Sources -> String -> Pipeline.Lookup
lookupIn sources project name =
    Dict.get project sources |> Maybe.andThen (Dict.get name)


type alias Options =
    { check : Bool, reportAll : Maybe String, classifyStatic : Bool }


config : Program.Config Options
config =
    Program.config
        |> Program.add
            (OptionsParser.build Options
                |> OptionsParser.with (Option.flag "check")
                |> OptionsParser.with (Option.optionalKeywordArg "report-all-refusals")
                |> OptionsParser.with (Option.flag "classify-static")
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


entry : Library -> Choices -> Sources -> Test -> BackendTask FatalError (Maybe Entry)
entry lib choices sources t =
    BackendTask.File.rawFile t.path
        |> BackendTask.allowFatal
        |> BackendTask.andThen
            (\source ->
                let
                    directives =
                        Directives.read source
                in
                if List.member "elm-spec" directives.tags && not directives.helper then
                    let
                        outcome =
                            case Pipeline.translateIn lib (lookupIn sources t.project) { project = t.project, name = t.name, defName = defNameOf t } source directives of
                                Translated tr ->
                                    case ( tr.kind, Dict.get (t.project ++ "/" ++ t.name) choices ) of
                                        ( "worker", Just fields ) ->
                                            Translated { tr | lean = Choices.apply fields tr.lean }

                                        _ ->
                                            Translated tr

                                refused ->
                                    refused

                        paths =
                            case outcome of
                                Translated tr ->
                                    tr.sources

                                Refused _ ->
                                    [ t.path ]
                    in
                    paths
                        |> List.map (\path -> sha256 path |> BackendTask.map (\sha -> { path = path, sha = sha }))
                        |> BackendTask.sequence
                        |> BackendTask.map
                            (\hashed ->
                                Just
                                    { test = t
                                    , sha = hashed |> List.filter (\h -> h.path == t.path) |> List.head |> Maybe.map .sha |> Maybe.withDefault ""
                                    , outcome = outcome
                                    , defName = defNameOf t
                                    , source = source
                                    , sources = hashed
                                    }
                            )

                else
                    BackendTask.succeed Nothing
            )


type alias Shard =
    { name : String, entries : List ( Entry, String ), worker : Bool }


{-| The translated entries of one kind (`view` or `worker`), with their Lean text.
-}
translatedOf : String -> List Entry -> List ( Entry, String )
translatedOf kind =
    List.filterMap
        (\e ->
            case e.outcome of
                Translated t ->
                    if t.kind == kind then
                        Just ( e, t.lean )

                    else
                        Nothing

                Refused _ ->
                    Nothing
        )


{-| The shards of the translated tests: the view programs in the buckets of `viewBounds`, then the
worker tests (Prog/Worker.lean), whose theorems are statements about executions, in the one shard
`Worker01` (35 tests; hand-written proofs in Prog/ import it by that name).
-}
shards : List Entry -> List Shard
shards entries =
    viewShards entries
        ++ (case translatedOf "worker" entries of
                [] ->
                    []

                ws ->
                    [ { name = "Worker01", entries = ws, worker = True } ]
           )


viewShards : List Entry -> List Shard
viewShards entries =
    translatedOf "view" entries
        |> bucketed viewBounds (\( e, _ ) -> e.test.project ++ "/" ++ e.test.name)
        |> List.map (\( b, es ) -> { name = bucketName b, entries = es, worker = False })


header : String
header =
    "/- Generated by definition/tools/src/Translate.elm from the tests in tests/. Do not edit. -/\n"


shardFile : Shard -> String
shardFile shard =
    if shard.worker then
        header
            ++ "import StandardElmMech.Examples\nimport StandardElmMech.Prog.Worker\n\nnamespace StandardElm\nopen StandardElm.D\n\n"
            ++ String.join "\n\n" (List.map Tuple.second shard.entries)
            ++ "\n\n/-- The worker tests of this shard. -/\ndef shard_"
            ++ shard.name
            ++ " : List Prog.WorkerTest :=\n  ["
            ++ String.join ",\n   " (List.map (\( e, _ ) -> workerName e) shard.entries)
            ++ "]\n\nend StandardElm\n"

    else
        header
            ++ "import StandardElmMech.Examples\n\nnamespace StandardElm\nopen StandardElm.D\n\n"
            ++ String.join "\n\n" (List.map Tuple.second shard.entries)
            ++ "\n\n/-- The programs of this shard. -/\ndef shard_"
            ++ shard.name
            ++ " : List Program :=\n  ["
            ++ String.join ",\n   " (List.map (\( e, _ ) -> e.defName) shard.entries)
            ++ "]\n\nend StandardElm\n"


{-| The tests of a shard whose CHECK-NOT lines are proved by hand (`Prog/Inv/<Test>.lean`).
-}
handCheckNots : Shard -> List String
handCheckNots shard =
    shard.entries
        |> List.filterMap
            (\( e, _ ) ->
                case e.outcome of
                    Translated t ->
                        if List.isEmpty t.checkNots then
                            Nothing

                        else
                            Just e.test.name

                    Refused _ ->
                        Nothing
            )


{-| The worker test's name: `w_<project>_<Name>` for the program `g_<project>_<Name>`.
-}
workerName : Entry -> String
workerName e =
    "w" ++ String.dropLeft 1 e.defName


allFile : List Shard -> String
allFile all =
    let
        ( workers, views ) =
            List.partition .worker all
    in
    header
        ++ String.concat (List.map (\s -> "import StandardElmMech.Generated." ++ s.name ++ "\n") all)
        ++ "\nnamespace StandardElm\n\n/-- Every shard of generated programs, by name. -/\ndef generatedShards : List (String × List Program) :=\n  ["
        ++ String.join ",\n   " (List.map (\s -> "(\"" ++ s.name ++ "\", shard_" ++ s.name ++ ")") views)
        ++ "]\n\n/-- Every generated program. -/\ndef generatedPrograms : List Program :=\n  generatedShards.foldr (fun s acc => s.2 ++ acc) []\n\n/-- Every shard of generated worker tests, by name. -/\ndef generatedWorkerShards : List (String × List Prog.WorkerTest) :=\n  ["
        ++ String.join ",\n   " (List.map (\s -> "(\"" ++ s.name ++ "\", shard_" ++ s.name ++ ")") workers)
        ++ "]\n\n/-- Every generated worker test. -/\ndef generatedWorkers : List Prog.WorkerTest :=\n  generatedWorkerShards.foldr (fun s acc => s.2 ++ acc) []\n\nend StandardElm\n"


checksFile : Shard -> String
checksFile shard =
    if shard.worker then
        header
            ++ "import StandardElmMech.Generated."
            ++ shard.name
            ++ "\nimport StandardElmMech.WorkerTheorems\nimport StandardElmMech.Eff.Normalise\n"
            ++ String.concat (List.map (\n -> "import StandardElmMech.Prog.Inv." ++ n ++ "\n") (handCheckNots shard))
            ++ "\nnamespace StandardElm\nopen StandardElm.D\n\n/-! One theorem per worker test of this shard (`t_<project>_<Test>`), generated by\n    `#worker_theorems` (WorkerTheorems.lean): some execution the book allows, under the test's\n    host, has a log that meets every check (`Prog.WorkerTest.Holds`). -/\n#worker_theorems"
            ++ String.concat (List.map (\( e, _ ) -> "\n  " ++ workerName e) shard.entries)
            ++ "\n\n"
            ++ portsCanon shard.name ("(shard_" ++ shard.name ++ ".map (·.prog))")
            ++ "\nend StandardElm\n"

    else
        header
            ++ "import StandardElmMech.Generated."
            ++ shard.name
            ++ "\nimport StandardElmMech.Theorems\nimport StandardElmMech.Eff.Normalise\n\nnamespace StandardElm\nopen StandardElm.D\n\n/-! One theorem per program of this shard (`t_<project>_<Test>`), generated by\n    `#mod_program_theorems` (Theorems.lean): the program in module form, and every check as a\n    statement about the log of its evaluation (`ViewChecks`), or `NoMeaning`. -/\n#mod_program_theorems"
            ++ String.concat (List.map (\( e, _ ) -> "\n  " ++ e.defName) shard.entries)
            ++ "\n\n"
            ++ portsCanon shard.name ("shard_" ++ shard.name)
            ++ "\nend StandardElm\n"


{-| The theorem that every port of every program of a shard has a canonical payload type (the
fields of every record type strictly increasing by label, D7), checked by the kernel.
-}
portsCanon : String -> String -> String
portsCanon name programs =
    "/-- Every port of every program of this shard, its helper modules' included, has a canonical\n    payload type (D7). -/\ntheorem ports_canon_"
        ++ name
        ++ " : "
        ++ programs
        ++ ".all (fun g => (g.ports ++ g.helpers.flatMap (·.ports)).all (fun p => p.2.2.canonB)) = true := by\n  decide +kernel\n"


rootRegion : List Shard -> String
rootRegion all =
    String.join "\n"
        ("import StandardElmMech.Generated.All"
            :: List.map (\s -> "import StandardElmMech.Generated.Checks" ++ s.name) all
            ++ [ "import StandardElmMech.Generated.SrcAll", "import StandardElmMech.Generated.SynAll" ]
        )


manifest : String -> Dict String Encode.Value -> List Entry -> String
manifest toolsSha srcByTest entries =
    let
        encodeEntry e shardOf =
            Encode.object
                ([ ( "project", Encode.string e.test.project )
                 , ( "name", Encode.string e.test.name )
                 , ( "sha256", Encode.string e.sha )
                 , ( "sources", Encode.list (\h -> Encode.object [ ( "path", Encode.string h.path ), ( "sha256", Encode.string h.sha ) ]) e.sources )
                 ]
                    ++ (Dict.get (e.test.project ++ "/" ++ e.test.name) srcByTest |> Maybe.map (\x -> [ ( "src", x ) ]) |> Maybe.withDefault [])
                    ++ (case e.outcome of
                            Translated t ->
                                [ ( "status", Encode.string "translated" )
                                , ( "shard", Encode.string (Maybe.withDefault "" shardOf) )
                                , ( "def", Encode.string e.defName )
                                , ( "checks", Encode.int t.checks )
                                , ( "kind", Encode.string t.kind )
                                , ( "native", Encode.bool t.native )
                                ]
                                    ++ (case t.host of
                                            Just h ->
                                                [ ( "host", Encode.string h )
                                                , ( "flags", t.flags |> Maybe.map Encode.string |> Maybe.withDefault Encode.null )
                                                ]

                                            Nothing ->
                                                []
                                       )
                                    ++ (if List.isEmpty t.checkNots then
                                            []

                                        else
                                            [ ( "checkNots", Encode.list Encode.string t.checkNots ) ]
                                       )
                                    ++ (if List.isEmpty t.dropped then
                                            []

                                        else
                                            [ ( "dropped", Encode.list Encode.string t.dropped ) ]
                                       )
                                    ++ (if List.isEmpty t.library then
                                            []

                                        else
                                            [ ( "library", Encode.list Encode.string t.library ) ]
                                       )
                                    ++ [ ( "lean", Encode.string t.lean ) ]

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
outputs : String -> Dict String Encode.Value -> List Entry -> String -> Result String (List Output)
outputs toolsSha srcByTest entries rootSource =
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
                       , { path = manifestPath, body = manifest toolsSha srcByTest entries }
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
        (\options ->
            let
                check =
                    options.check
            in
            tests
                |> BackendTask.andThen
                    (\ts ->
                        BackendTask.map3 (\a b c -> ( a, b, c ))
                            (BackendTask.File.jsonFile Choices.decoder Choices.path |> BackendTask.allowFatal)
                            (readSources ts)
                            libraryTextsTask
                            |> BackendTask.andThen
                                (\( choices, sources, texts ) ->
                                    case buildLibrary texts of
                                        Err problem ->
                                            BackendTask.fail (FatalError.fromString ("the library: " ++ problem))

                                        Ok built ->
                                            BackendTask.sequence (List.map (entry built.library choices sources) ts)
                                                |> BackendTask.map (\es -> ( ( ts, sources, built ), List.filterMap identity es ))
                                )
                    )
                |> BackendTask.andThen
                    (\( ( allTests, sources, built ), entries ) ->
                        case options.reportAll of
                            Just path ->
                                toolsSha256
                                    |> BackendTask.andThen
                                        (\toolsSha ->
                                            Script.log (summary entries)
                                                |> BackendTask.andThen
                                                    (\_ ->
                                                        let
                                                            body =
                                                                refusalReport built.library toolsSha sources allTests entries
                                                        in
                                                        Script.log ("report: " ++ String.fromInt (String.length body) ++ " characters")
                                                            |> BackendTask.andThen (\_ -> Script.writeFile { path = path, body = body } |> BackendTask.allowFatal)
                                                    )
                                                |> BackendTask.andThen (\_ -> Script.log ("written: " ++ path))
                                        )

                            Nothing ->
                                BackendTask.map5 (\a b c d e -> ( ( a, b ), ( c, d ), e ))
                                    (BackendTask.File.rawFile (mech ++ "StandardElmMech.lean") |> BackendTask.allowFatal)
                                    toolsSha256
                                    bookLabelsTask
                                    (BackendTask.map2 Tuple.pair
                                        (BackendTask.File.jsonFile SB.basisDecoder staticBasisPath |> BackendTask.allowFatal)
                                        (sha256 staticBasisPath)
                                    )
                                    libraryTask
                                    |> BackendTask.andThen
                                        (\( ( rootSource, toolsSha ), ( labels, ( basis, basisSha ) ), libs ) ->
                                            let
                                                cls =
                                                    classification labels basis basisSha allTests sources

                                                src =
                                                    sourceSyntax allTests sources
                                            in
                                            if options.classifyStatic then
                                                Script.log (cls.summary ++ "\n" ++ cls.lists)

                                            else
                                                case Result.map2 Tuple.pair (outputs toolsSha src.byTest entries rootSource |> Result.mapError (\p -> "StandardElmMech.lean: " ++ p)) (staticLibrary libs) of
                                                    Err problem ->
                                                        BackendTask.fail (FatalError.fromString problem)

                                                    Ok ( files0, libFile ) ->
                                                        let
                                                            files =
                                                                files0
                                                                    ++ [ { path = classificationPath, body = cls.body } ]
                                                                    ++ src.files
                                                                    ++ [ libFile, built.file ]
                                                        in
                                                        Script.log (summary entries ++ "\n" ++ src.summary)
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


{-| The manifest's `toolsSha256`: the hash of the hashes of the translator's sources and of the
parser it vendors (plans/eco-parser.md, E13).
-}
toolsSha256 : BackendTask FatalError String
toolsSha256 =
    BackendTask.map2 (\a b -> a ++ "\n" ++ b)
        (BackendTask.Custom.run "sha256Tree" (Encode.string "definition/tools/src") Decode.string |> BackendTask.allowFatal)
        (BackendTask.Custom.run "sha256Tree" (Encode.string "definition/tools/vendor") Decode.string |> BackendTask.allowFatal)
        |> BackendTask.andThen (\both -> BackendTask.Custom.run "sha256Text" (Encode.string both) Decode.string |> BackendTask.allowFatal)


{-| The library values of the test basis (decision D2 (b)): module, vendored file, values. The
values are those the compile-success tests use (step 7's `library:` needs).
-}
libraryValues : List ( String, String, List String )
libraryValues =
    [ ( "Array", "definition/library/elm-core-1.0.5/src/Array.elm", [ "append", "empty", "fromList", "initialize", "map", "push", "toList" ] )
    , ( "Json.Encode", "definition/library/elm-json-1.1.3/src/Json/Encode.elm", [ "bool", "encode", "float", "int", "list", "null", "object", "string" ] )
    , ( "List", "definition/library/elm-core-1.0.5/src/List.elm", [ "foldl", "foldr", "head", "length", "map", "map2", "range", "sum" ] )
    , ( "Maybe", "definition/library/elm-core-1.0.5/src/Maybe.elm", [ "andThen", "map", "withDefault" ] )
    , ( "Result", "definition/library/elm-core-1.0.5/src/Result.elm", [ "map" ] )
    , ( "String", "definition/library/elm-core-1.0.5/src/String.elm", [ "length" ] )
    , ( "Tuple", "definition/library/elm-core-1.0.5/src/Tuple.elm", [ "first", "second" ] )
    ]


libraryTask : BackendTask FatalError (List ( ( String, String, List String ), String ))
libraryTask =
    libraryValues
        |> List.map (\(( _, path, _ ) as lv) -> BackendTask.File.rawFile path |> BackendTask.allowFatal |> BackendTask.map (\src -> ( lv, src )))
        |> BackendTask.sequence


{-| Generated/StaticLibrary.lean: the annotations of the library values, as source syntax.
-}
staticLibrary : List ( ( String, String, List String ), String ) -> Result String Output
staticLibrary libs =
    let
        defName m =
            "lib_" ++ String.replace "." "_" m

        one ( ( m, path, names ), src ) =
            case Parse.parse src of
                Err e ->
                    Err (path ++ ": does not parse (" ++ e ++ ")")

                Ok file ->
                    case Source.annotations { path = path, source = src } file names of
                        Err problem ->
                            Err (problem.at ++ ": " ++ problem.reason)

                        Ok text ->
                            Ok ("/-- From " ++ path ++ ". -/\ndef " ++ defName m ++ " : ModId × List (Var × Src.STy) :=\n  (\"" ++ m ++ "\", " ++ text ++ ")")
    in
    libs
        |> List.map one
        |> List.foldr (Result.map2 (::)) (Ok [])
        |> Result.map
            (\defs ->
                { path = generatedDir ++ "StaticLibrary.lean"
                , body =
                    header
                        ++ "import StandardElmMech.Src.Notation\n\nnamespace StandardElm.Stat\nopen StandardElm (Var ModId)\n\n"
                        ++ String.join "\n\n" defs
                        ++ "\n\n/-- The library values of the test basis (D2 (b)), by module. -/\ndef libModules : List (ModId × List (Var × Src.STy)) :=\n  ["
                        ++ String.join ", " (List.map (\( ( m, _, _ ), _ ) -> defName m) libs)
                        ++ "]\n\nend StandardElm.Stat\n"
                }
            )


{-| The library values the translator evaluates (plans/library-elm-texts.md, step 1): module, vendored
file, values. Each is defined in elm/core 1.0.5 by Elm text that names only other Elm text, the
book's basic values and `List.cons`. A test may name them; the dynamic test basis binds them to the
values of their texts (`Lib.Btest`), which `Generated/Library.lean` holds as modules.
-}
evaluatedLibrary : List Library.Text
evaluatedLibrary =
    [ { modul = "List", path = "definition/library/elm-core-1.0.5/src/List.elm", values = [ "foldl", "foldr", "head", "length", "map", "sum" ] }
    , { modul = "Maybe", path = "definition/library/elm-core-1.0.5/src/Maybe.elm", values = [ "andThen", "map", "withDefault" ] }
    , { modul = "Result", path = "definition/library/elm-core-1.0.5/src/Result.elm", values = [ "map" ] }
    , { modul = "Tuple", path = "definition/library/elm-core-1.0.5/src/Tuple.elm", values = [ "first", "second" ] }
    ]


libraryTextsTask : BackendTask FatalError (List ( Library.Text, String ))
libraryTextsTask =
    evaluatedLibrary
        |> List.map (\t -> BackendTask.File.rawFile t.path |> BackendTask.allowFatal |> BackendTask.map (\src -> ( t, src )))
        |> BackendTask.sequence


{-| The library the tests may name and `Generated/Library.lean` (`LibraryTexts.build`).
-}
buildLibrary : List ( Library.Text, String ) -> Result String { library : Library, file : Output }
buildLibrary texts =
    LibraryTexts.build texts
        |> Result.map (\b -> { library = b.library, file = { path = generatedDir ++ "Library.lean", body = header ++ b.lean } })


staticBasisPath : String
staticBasisPath =
    "definition/mechanisation/static-basis.json"


classificationPath : String
classificationPath =
    "definition/mechanisation/static-classification.json"


{-| The labels of the book (`\label`, `\citelabel`, `\citealso`, `\defnrule`), from every chapter.
-}
bookLabelsTask : BackendTask FatalError (Set String)
bookLabelsTask =
    Glob.succeed identity
        |> Glob.captureFilePath
        |> Glob.match (Glob.literal "definition/tex/")
        |> Glob.match Glob.wildcard
        |> Glob.match (Glob.literal ".tex")
        |> Glob.toBackendTask
        |> BackendTask.andThen
            (\paths ->
                paths
                    |> List.map (\p -> BackendTask.File.rawFile p |> BackendTask.allowFatal)
                    |> BackendTask.combine
                    |> BackendTask.map (String.join "\n" >> Classify.bookLabels)
            )


{-| The modules of a test's program: the test, then every module it imports, transitively, that
is a file of its project's sources (a visited set follows a cycle once). Each is parsed and, if it
parses, checked by the front end (`Translate.FrontEnd`): its refusal is its parse failure (at its
path, with `Parse.describe`'s text) or the front end's first (at `path:row:col`).
-}
programModules : Sources -> Test -> String -> List Classify.ModuleParse
programModules sources t source =
    let
        parse name path text =
            case Parse.parse text of
                Err detail ->
                    { path = path, name = name, file = Nothing, refusal = Just { reason = "parse", at = path, detail = Just detail } }

                Ok file ->
                    { path = path
                    , name = name
                    , file = Just file
                    , refusal =
                        FrontEnd.check { path = path, source = text } file
                            |> List.head
                            |> Maybe.map (\r -> { reason = r.reason, at = path ++ ":" ++ Region.startText r.at, detail = Nothing })
                    }

        importsOf m =
            m.file
                |> Maybe.map (\f -> List.map .name (Parse.importsOf f))
                |> Maybe.withDefault []

        go queue visited acc =
            case queue of
                [] ->
                    acc

                name :: rest ->
                    if Set.member name visited then
                        go rest visited acc

                    else
                        case Dict.get t.project sources |> Maybe.andThen (Dict.get name) of
                            Just s ->
                                let
                                    m =
                                        parse name s.path s.source
                                in
                                go (rest ++ importsOf m) (Set.insert name visited) (acc ++ [ m ])

                            Nothing ->
                                go rest (Set.insert name visited) acc

        first =
            parse t.name t.path source
    in
    go (importsOf first) (Set.singleton t.name) [ first ]


{-| The static classification of every `elm-spec` test (plans/lean-full-definition/step-07-classify.md):
the JSON, the summary, and the tests of each class.
-}
classification : Set String -> SB.Basis -> String -> List Test -> Sources -> { body : String, summary : String, lists : String }
classification labels basis basisSha allTests sources =
    let
        selected =
            allTests
                |> List.filterMap
                    (\t ->
                        Dict.get t.project sources
                            |> Maybe.andThen (Dict.get t.name)
                            |> Maybe.andThen
                                (\s ->
                                    let
                                        d =
                                            Directives.read s.source
                                    in
                                    if List.member "elm-spec" d.tags && not d.helper then
                                        Just ( t, s.source, d )

                                    else
                                        Nothing
                                )
                    )

        helperSet project =
            Dict.get project sources |> Maybe.map (Dict.keys >> Set.fromList) |> Maybe.withDefault Set.empty

        titleOf d =
            d.lines
                |> List.head
                |> Maybe.andThen
                    (\l ->
                        if String.startsWith "-- " l.text && String.endsWith " -" l.text then
                            Just (l.text |> String.dropLeft 3 |> String.dropRight 2 |> String.trim)

                        else
                            Nothing
                    )

        errors =
            selected
                |> List.filter (\( _, _, d ) -> List.member "compile-error" d.refusals)
                |> List.map
                    (\( t, source, d ) ->
                        Classify.classifyError { labels = labels, overrides = ClassifyOverrides.overrides }
                            { project = t.project, name = t.name, tags = d.tags, title = titleOf d, modules = programModules sources t source }
                    )

        successes =
            selected
                |> List.filter (\( _, _, d ) -> not (List.member "compile-error" d.refusals))
                |> List.map
                    (\( t, source, _ ) ->
                        let
                            mods =
                                programModules sources t source
                        in
                        Classify.classifySuccess basis
                            { project = t.project, name = t.name, modules = mods, helpers = Set.remove t.name (helperSet t.project) }
                    )

        countBy key xs order =
            order |> List.map (\k -> ( k, List.length (List.filter (\x -> key x == k) xs) ))

        errorOrder =
            [ "parse-fail", "syntax-refused", "lexical-accepted", "syntactic", "further", "fixity-inference", "static-deterministic", "inference" ]

        successOrder =
            [ "B0", "harness", "library", "helper", "outside", "parse-fail" ]

        errorCounts =
            countBy .class errors errorOrder

        successCounts =
            countBy .basis successes successOrder

        showCounts cs =
            cs |> List.map (\( k, n ) -> k ++ " " ++ String.fromInt n) |> String.join ", "

        encodeModules ms =
            Encode.list (\( p, ok ) -> Encode.object [ ( "path", Encode.string p ), ( "parse", Encode.string (okStr ok) ) ]) ms

        okStr ok =
            if ok then
                "ok"

            else
                "fail"

        maybeStr m =
            m |> Maybe.map Encode.string |> Maybe.withDefault Encode.null

        body =
            Encode.encode 2
                (Encode.object
                    [ ( "generatedBy", Encode.string "definition/tools/src/Translate.elm" )
                    , ( "staticBasisSha256", Encode.string basisSha )
                    , ( "counts"
                      , Encode.object
                            [ ( "compileError", Encode.object (List.map (\( k, n ) -> ( k, Encode.int n )) errorCounts) )
                            , ( "compileSuccess", Encode.object (List.map (\( k, n ) -> ( k, Encode.int n )) successCounts) )
                            ]
                      )
                    , ( "compileError"
                      , Encode.list
                            (\e ->
                                Encode.object
                                    [ ( "project", Encode.string e.project )
                                    , ( "name", Encode.string e.name )
                                    , ( "modules", encodeModules e.modules )
                                    , ( "parse", Encode.string (okStr e.parse) )
                                    , ( "rules", Encode.list Encode.string e.rules )
                                    , ( "rule", maybeStr e.rule )
                                    , ( "class", Encode.string e.class )
                                    , ( "subclass", maybeStr e.subclass )
                                    , ( "step", e.step |> Maybe.map Encode.int |> Maybe.withDefault Encode.null )
                                    , ( "trust", Encode.list Encode.string e.trust )
                                    , ( "title", maybeStr e.title )
                                    , ( "override", maybeStr e.override )
                                    ]
                            )
                            errors
                      )
                    , ( "compileSuccess"
                      , Encode.list
                            (\c ->
                                Encode.object
                                    [ ( "project", Encode.string c.project )
                                    , ( "name", Encode.string c.name )
                                    , ( "modules", encodeModules c.modules )
                                    , ( "parse", Encode.string (okStr c.parse) )
                                    , ( "basis", Encode.string c.basis )
                                    , ( "needs", Encode.list Encode.string c.needs )
                                    , ( "main", Encode.string c.main )
                                    , ( "mainAnnotated", Encode.bool c.mainAnnotated )
                                    ]
                            )
                            successes
                      )
                    ]
                )
                ++ "\n"

        lists =
            (errorOrder
                |> List.map (\k -> "compile-error " ++ k ++ ": " ++ String.join ", " (errors |> List.filter (\e -> e.class == k) |> List.map .name))
            )
                ++ (successOrder
                        |> List.map (\k -> "compile-success " ++ k ++ ": " ++ String.join ", " (successes |> List.filter (\c -> c.basis == k && k /= "harness") |> List.map .name))
                   )
                |> String.join "\n"
    in
    { body = body
    , summary =
        "static classification: "
            ++ String.fromInt (List.length selected)
            ++ " elm-spec tests\n  compile-error "
            ++ String.fromInt (List.length errors)
            ++ ": "
            ++ showCounts errorCounts
            ++ "\n  compile-success "
            ++ String.fromInt (List.length successes)
            ++ ": "
            ++ showCounts successCounts
    , lists = lists
    }


{-| The source syntax of every `elm-spec` test whose program parses (plan step 8): the shards
`Generated/Src<Bucket>.lean` (the buckets of `srcBounds`), `Generated/SrcAll.lean`, a file of
syntactic theorems per shard (`Generated/Syn<Bucket>.lean`), each test's outcome for the manifest,
and the summary line.
-}
sourceSyntax : List Test -> Sources -> { files : List Output, byTest : Dict String Encode.Value, summary : String }
sourceSyntax allTests sources =
    let
        selected =
            allTests
                |> List.filterMap
                    (\t ->
                        Dict.get t.project sources
                            |> Maybe.andThen (Dict.get t.name)
                            |> Maybe.andThen
                                (\s ->
                                    let
                                        d =
                                            Directives.read s.source
                                    in
                                    if List.member "elm-spec" d.tags && not d.helper then
                                        Just ( t, s.source )

                                    else
                                        Nothing
                                )
                    )

        defOf t =
            "s_" ++ String.replace "-" "_" t.project ++ "_" ++ t.name

        outcome ( t, source ) =
            let
                mods =
                    programModules sources t source

                sourceOf m =
                    Dict.get t.project sources |> Maybe.andThen (Dict.get m.name) |> Maybe.map .source |> Maybe.withDefault source
            in
            case List.filterMap .refusal mods of
                refusal :: _ ->
                    -- a module that does not parse, or that the front end refuses, is not written
                    -- (plans/eco-parser.md, E7)
                    ( t, Err refusal, mods )

                [] ->
                    let
                        ordered =
                            List.drop 1 mods ++ List.take 1 mods
                    in
                    ( t
                    , Source.program { project = t.project, name = t.name, defName = defOf t }
                        (List.filterMap (\m -> m.file |> Maybe.map (\f -> { path = m.path, source = sourceOf m, file = f })) ordered)
                        |> Result.mapError (\p -> { reason = p.reason, at = p.at, detail = Nothing })
                    , mods
                    )

        results =
            List.map outcome selected

        written =
            results |> List.filterMap (\( t, r, mods ) -> Result.toMaybe r |> Maybe.map (\lean -> ( t, lean, mods )))

        srcShards =
            written
                |> bucketed srcBounds (\( t, _, _ ) -> t.project ++ "/" ++ t.name)
                |> List.map (\( b, chunk ) -> ( "Src" ++ bucketName b, chunk ))

        shardOf =
            srcShards |> List.concatMap (\( n, chunk ) -> List.map (\( t, _, _ ) -> ( t.project ++ "/" ++ t.name, n )) chunk) |> Dict.fromList

        shardFileText ( n, chunk ) =
            { path = generatedDir ++ n ++ ".lean"
            , body =
                header
                    ++ "import StandardElmMech.Src.Notation\n\nnamespace StandardElm\nset_option maxRecDepth 100000\n\n"
                    ++ String.join "\n\n" (List.map (\( _, lean, _ ) -> lean) chunk)
                    ++ "\n\n/-- The programs of this shard, by test name. -/\ndef srcShard_"
                    ++ n
                    ++ " : List (String × Src.SProgram) :=\n  ["
                    ++ String.join ",\n   " (List.map (\( t, _, _ ) -> "(" ++ "\"" ++ t.name ++ "\", " ++ defOf t ++ ")") chunk)
                    ++ "]\n\nend StandardElm\n"
            }

        allText =
            { path = generatedDir ++ "SrcAll.lean"
            , body =
                header
                    ++ String.concat (List.map (\( n, _ ) -> "import StandardElmMech.Generated." ++ n ++ "\n") srcShards)
                    ++ "\nnamespace StandardElm\n\n/-- Every shard of source programs, by name: test name and program. -/\ndef srcShards : List (String × List (String × Src.SProgram)) :=\n  ["
                    ++ String.join ",\n   " (List.map (\( n, _ ) -> "(\"" ++ n ++ "\", srcShard_" ++ n ++ ")") srcShards)
                    ++ "]\n\nend StandardElm\n"
            }

        -- the theorems of the restrictions, a file per source shard, so that a change to one source
        -- shard rebuilds one (one file for all needs more than the memory budget, 2026-11-12: 6.5 GB)
        synGroups =
            srcShards
                |> List.map (\( n, _ ) -> ( "Syn" ++ String.dropLeft 3 n, [ n ] ))

        synFile ( g, names ) =
            { path = generatedDir ++ g ++ ".lean"
            , body =
                header
                    ++ String.concat (List.map (\n -> "import StandardElmMech.Generated." ++ n ++ "\n") names)
                    ++ "import StandardElmMech.Src.SynCommand\n\nnamespace StandardElm\n\n/-- The programs of this file's source shards. -/\ndef synShards_"
                    ++ g
                    ++ " : List (String × List (String × Src.SProgram)) :=\n  ["
                    ++ String.join ",\n   " (List.map (\n -> "(\"" ++ n ++ "\", srcShard_" ++ n ++ ")") names)
                    ++ "]\n\n/-! One theorem per written program (plan step 8): it meets the AST-decidable restrictions\n    (`syn_<project>_<Test>`), or it does not, with one theorem for each restriction it breaks\n    (`nosyn_...`). Generated by `#syn_theorems` (Src/SynCommand.lean). -/\n#syn_theorems synShards_"
                    ++ g
                    ++ "\n\nend StandardElm\n"
            }

        byTest =
            results
                |> List.map
                    (\( t, r, mods ) ->
                        ( t.project ++ "/" ++ t.name
                        , case r of
                            Ok _ ->
                                Encode.object
                                    [ ( "status", Encode.string "written" )
                                    , ( "shard", Encode.string (Dict.get (t.project ++ "/" ++ t.name) shardOf |> Maybe.withDefault "") )
                                    , ( "def", Encode.string (defOf t) )
                                    , ( "modules", Encode.list (\m -> Encode.string m.path) mods )
                                    ]

                            Err problem ->
                                Encode.object
                                    ([ ( "status", Encode.string "refused" )
                                     , ( "reason", Encode.string problem.reason )
                                     , ( "at", Encode.string problem.at )
                                     ]
                                        ++ (problem.detail |> Maybe.map (\d -> [ ( "detail", Encode.string d ) ]) |> Maybe.withDefault [])
                                    )
                        )
                    )
                |> Dict.fromList

        refusedReasons =
            results
                |> List.filterMap
                    (\( _, r, _ ) ->
                        case r of
                            Err problem ->
                                Just problem.reason

                            Ok _ ->
                                Nothing
                    )

        reasonCounts =
            refusedReasons
                |> List.foldl (\x d -> Dict.update x (\c -> Just (Maybe.withDefault 0 c + 1)) d) Dict.empty
                |> Dict.toList
                |> List.map (\( k, n ) -> k ++ " " ++ String.fromInt n)
    in
    { files =
        List.map shardFileText srcShards
            ++ [ allText
               , { path = generatedDir ++ "SynAll.lean"
                 , body =
                    header
                        ++ String.concat (List.map (\( g, _ ) -> "import StandardElmMech.Generated." ++ g ++ "\n") synGroups)
                 }
               ]
            ++ List.map synFile synGroups
    , byTest = byTest
    , summary =
        "source syntax: "
            ++ String.fromInt (List.length written)
            ++ " written, "
            ++ String.fromInt (List.length refusedReasons)
            ++ " refused ("
            ++ String.join ", " reasonCounts
            ++ ")"
    }


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
        |> BackendTask.andThen (\_ -> staleFiles files)
        |> BackendTask.andThen
            (\stale ->
                stale
                    |> List.map (\path -> BackendTask.Custom.run "removeFile" (Encode.string path) (Decode.succeed ()) |> BackendTask.allowFatal)
                    |> BackendTask.sequence
                    |> BackendTask.andThen
                        (\_ ->
                            if List.isEmpty stale then
                                BackendTask.succeed ()

                            else
                                Script.log ("removed: " ++ String.join ", " stale)
                        )
            )


{-| The Lean files of `Generated/` that this translator wrote (they start with its header) and that
it no longer writes: a shard whose bucket is now empty, or a file of an earlier naming of the shards.
-}
staleFiles : List Output -> BackendTask FatalError (List String)
staleFiles files =
    let
        written =
            Set.fromList (List.map .path files)
    in
    Glob.succeed (\path _ -> path)
        |> Glob.captureFilePath
        |> Glob.match (Glob.literal generatedDir)
        |> Glob.capture Glob.wildcard
        |> Glob.match (Glob.literal ".lean")
        |> Glob.toBackendTask
        |> BackendTask.andThen
            (\paths ->
                paths
                    |> List.filter (\path -> not (Set.member path written))
                    |> List.map
                        (\path ->
                            BackendTask.File.rawFile path
                                |> BackendTask.allowFatal
                                |> BackendTask.map
                                    (\body ->
                                        if String.startsWith header body then
                                            Just path

                                        else
                                            Nothing
                                    )
                        )
                    |> BackendTask.combine
                    |> BackendTask.map (List.filterMap identity >> List.sort)
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
        |> BackendTask.map2 (\stale changes -> changes ++ List.map (\path -> Just ("would remove: " ++ path)) stale) (staleFiles files)
        |> BackendTask.andThen
            (\changes ->
                case List.filterMap identity changes of
                    [] ->
                        Script.log "Lean translations are up to date."

                    cs ->
                        Script.log (String.join "\n" cs ++ "\n" ++ String.fromInt (List.length cs) ++ " file(s) differ from what the translator would write; run it, then the mechanisation stage.")
            )


{-| The report of every refusal of every `elm-spec` test (step 0 of plans/lean-full-definition.md),
with the facts the inventory script needs: the modules a test uses beyond the default imports, its
imports that name a module among its project's sources, and whether it is a worker or a port module.
-}
refusalReport : Library -> String -> Sources -> List Test -> List Entry -> String
refusalReport lib toolsSha sources allTests entries =
    let
        encodeFound f =
            Encode.object
                ([ ( "stage", Encode.string (Pipeline.stageName f.stage) )
                 , ( "reason", Encode.string f.reason )
                 ]
                    ++ (f.at |> Maybe.map (\a -> [ ( "at", Encode.string a ) ]) |> Maybe.withDefault [])
                    ++ (f.detail |> Maybe.map (\d -> [ ( "detail", Encode.string d ) ]) |> Maybe.withDefault [])
                )

        encodeEntry e =
            let
                found =
                    Pipeline.translateAllIn lib (lookupIn sources e.test.project) { project = e.test.project, name = e.test.name, defName = e.defName } e.source (Directives.read e.source)

                factFields =
                    case Parse.parse e.source of
                        Ok file ->
                            let
                                f =
                                    Convert.facts e.source file

                                local =
                                    f.imports
                                        |> List.filter
                                            (\m -> List.any (\t -> t.project == e.test.project && t.name == m) allTests)
                            in
                            [ ( "uses", Encode.list Encode.string f.uses )
                            , ( "localModules", Encode.list Encode.string local )
                            , ( "worker", Encode.bool f.worker )
                            , ( "ports", Encode.bool f.ports )
                            ]

                        Err _ ->
                            []
            in
            Encode.object
                ([ ( "project", Encode.string e.test.project )
                 , ( "name", Encode.string e.test.name )
                 , ( "status"
                   , Encode.string
                        (case e.outcome of
                            Translated _ ->
                                "translated"

                            Refused _ ->
                                "refused"
                        )
                   )
                 , ( "refusals", Encode.list encodeFound found )
                 ]
                    ++ factFields
                )
    in
    Encode.encode 2
        (Encode.object
            [ ( "generatedBy", Encode.string "definition/tools/src/Translate.elm --report-all-refusals" )
            , ( "toolsSha256", Encode.string toolsSha )
            , ( "tests", Encode.list encodeEntry entries )
            ]
        )
        ++ "\n"
