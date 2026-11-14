module Translate.Pipeline exposing (Found, Lookup, Outcome(..), Refusal, Stage(..), stageName, translate, translateAll, translateAllIn, translateAllWith, translateIn, translateWith)

{-| One test, from source to Lean or to the reason it is not translated: directives, parsing,
conversion (names, fragment, checks), inference, number specialisation, printing.
-}

import Dict
import Set exposing (Set)
import Translate.Convert as Convert exposing (ModuleSource)
import Translate.Directives as Directives exposing (Directives)
import Translate.FrontEnd as FrontEnd
import Translate.Infer as Infer
import Translate.Ir as Ir exposing (Decl(..), Expr(..), Name(..), TestProgram, anyExpr)
import Translate.Json as Json
import Translate.Library as Library exposing (Library)
import Translate.Parse as Parse exposing (Parsed)
import Translate.Region as Region
import Translate.Specialise as Specialise
import Translate.ToLean as ToLean


type alias Refusal =
    { reason : String, at : Maybe String, detail : Maybe String }


type Outcome
    = Translated
        { lean : String
        , checks : Int
        , sources : List String

        -- "view" or "worker"
        , kind : String

        -- whether the theorem is proved by `native_decide`
        , native : Bool

        -- a worker's host ("none" or "echo") and its FLAGS text (`Nothing`: absent, null)
        , host : Maybe String
        , flags : Maybe String

        -- the CHECK-NOT lines dropped (`Directives.checkNotsNotRequired`), with the reason
        , dropped : List String

        -- the patterns of the CHECK-NOT lines proved by hand (plan step 6)
        , checkNots : List String

        -- the core library values the program names, `M.x` (plans/library-elm-texts.md)
        , library : List String
        }
    | Refused Refusal


{-| The modules of a test's project, by name: the path and text of `tests/<project>/src/<M>.elm`.
-}
type alias Lookup =
    String -> Maybe { path : String, source : String }


{-| The modules of the basis (plan step 3): an import of one of them is never read from the
project's sources.
-}
basisModules : Set String
basisModules =
    Set.fromList [ "Basics", "List", "Maybe", "Result", "String", "Char", "Tuple", "Debug", "Platform", "Platform.Cmd", "Platform.Sub", "Array", "Bytes", "Json.Encode", "Json.Decode", "VirtualDom", "Html" ]


{-| The modules of a program in program order: depth-first post-order from the test, following
each module's imports in the order written, a module after the modules it imports and once, the
test last (<res:program-import-order>). An import of a module that is not among the project's
sources is left to the converter, which refuses it (`import:M`). An import cycle is refused. A
module that does not parse, or that the front end refuses (`Translate.FrontEnd`), is refused.
-}
resolve : Lookup -> ModuleSource -> Result Refusal (List ModuleSource)
resolve lookup main =
    visit lookup [ main.name ] [] main


visit : Lookup -> List String -> List ModuleSource -> ModuleSource -> Result Refusal (List ModuleSource)
visit lookup stack acc ms =
    let
        imported =
            Parse.importsOf ms.file
                |> List.map .name
                |> List.filter (\m -> not (Set.member m basisModules))
    in
    List.foldl
        (\name result ->
            result
                |> Result.andThen
                    (\done ->
                        if List.any (\d -> d.name == name) done then
                            Ok done

                        else if List.member name stack then
                            Err { reason = "import:cycle", at = Nothing, detail = Nothing }

                        else
                            case lookup name of
                                Nothing ->
                                    Ok done

                                Just helper ->
                                    parseModule helper.path helper.source
                                        |> Result.andThen (\file -> visit lookup (name :: stack) done { name = name, path = helper.path, source = helper.source, file = file })
                    )
        )
        (Ok acc)
        imported
        |> Result.map (\done -> done ++ [ ms ])


{-| A module parsed and checked by the front end (plans/eco-parser.md, E7): a parse failure is
refused as `parse`, with `Parse.describe`'s text; a module the front end refuses, with its reason,
at `path:row:col`.
-}
parseModule : String -> String -> Result Refusal Parsed
parseModule path source =
    case Parse.parse source of
        Err detail ->
            Err { reason = "parse", at = Nothing, detail = Just detail }

        Ok file ->
            case FrontEnd.check { path = path, source = source } file of
                r :: _ ->
                    Err { reason = r.reason, at = Just (path ++ ":" ++ Region.startText r.at), detail = Nothing }

                [] ->
                    Ok file


refuse : String -> Outcome
refuse reason =
    Refused { reason = reason, at = Nothing, detail = Nothing }


translate : { project : String, name : String, defName : String } -> String -> Directives -> Outcome
translate =
    translateWith (\_ -> Nothing)


translateWith : Lookup -> { project : String, name : String, defName : String } -> String -> Directives -> Outcome
translateWith =
    translateIn Library.empty


{-| A test's translation when its program may name the values of the core library `lib`.
-}
translateIn : Library -> Lookup -> { project : String, name : String, defName : String } -> String -> Directives -> Outcome
translateIn lib lookup info source directives0 =
    let
        directives =
            Directives.dropCheckNots info.name directives0
    in
    case directives.refusal of
        Just reason ->
            refuse reason

        Nothing ->
            if String.length source > largeProgram then
                -- a test of a compiler's limits (hundreds of fields or arguments, thousands of
                -- list elements): too large for the Lean encoding's code generator
                refuse "construct:large-program"

            else if List.member info.name largeComputations then
                refuse "construct:large-computation"

            else
                parseAndTranslate lib lookup info source directives


{-| A message of inference that is a reason of its own: `main` is not a view
(`construct:main-type`, `construct:main-shape`) or is a worker (`effects:worker`).
-}
isReason : String -> Bool
isReason message =
    String.startsWith "construct:" message || String.startsWith "effects" message


{-| The size, in characters, beyond which a test is taken as a test of a compiler's limits.
-}
largeProgram : Int
largeProgram =
    20000


{-| Tests of a compiler's limits whose programs are small but whose computations are not: more
steps than the Lean evaluator's fuel (100000), and too deep for the kernel. Their size cannot be
seen in the source, so they are named.
-}
largeComputations : List String
largeComputations =
    [ -- lists of 50000 and 150000 elements built while a wide record is live (a test of the GC)
      "WideRecordGcBitmapTest"

    -- a command nested 100000 deep in Cmd.batch (elm/core#1123)
    , "CoreIssue1123NestedCmdBatchStackOverflowTest"
    ]


{-| Tests whose theorems the kernel cannot check within the memory budget (6.5 GB per process),
proved by `native_decide` only; each entry is dated with its measured peak. None so far.
-}
kernelTooLarge : List String
kernelTooLarge =
    []


parseAndTranslate : Library -> Lookup -> { project : String, name : String, defName : String } -> String -> Directives -> Outcome
parseAndTranslate lib lookup info source directives =
    case parseModule (mainPath info) source of
        Err refusal ->
            Refused refusal

        Ok file ->
            case resolve lookup (mainSource info source file) of
                Err refusal ->
                    Refused refusal

                Ok sources ->
                    case Convert.convertProgram lib directives sources of
                        ( _, p :: _ ) ->
                            Refused
                                { reason = p.code
                                , at = Just (Region.startText p.at)
                                , detail = Nothing
                                }

                        ( program, [] ) ->
                            case Infer.inferWith lib program of
                                Err message ->
                                    if isReason message then
                                        Refused { reason = message, at = Nothing, detail = Nothing }

                                    else
                                        Refused { reason = "type", at = Nothing, detail = Just message }

                                Ok inferred ->
                                    case Specialise.specialiseWith lib program inferred of
                                        Err message ->
                                            if String.startsWith "basis:" message || String.startsWith "construct:" message then
                                                Refused { reason = message, at = Nothing, detail = Nothing }

                                            else
                                                Refused { reason = "number", at = Nothing, detail = Just message }

                                        Ok specialised ->
                                            let
                                                native =
                                                    specialised.native || List.member info.name kernelTooLarge

                                                library =
                                                    Library.used lib program

                                                programText =
                                                    ToLean.programDef info specialised.program specialised.kinds specialised.ports native library

                                                host =
                                                    echoHost specialised.program specialised.ports
                                            in
                                            Translated
                                                { lean =
                                                    case specialised.flags of
                                                        Just flagsType ->
                                                            programText
                                                                ++ "\n\n"
                                                                ++ ToLean.workerDef info
                                                                    flagsType
                                                                    (directives.flags |> Maybe.map Json.toLean |> Maybe.withDefault ".null")
                                                                    host
                                                                    directives.checkNots

                                                        Nothing ->
                                                            programText
                                                , checks = List.length specialised.program.checks
                                                , sources = List.map .path sources
                                                , kind =
                                                    if specialised.flags == Nothing then
                                                        "view"

                                                    else
                                                        "worker"
                                                , native = native
                                                , host =
                                                    specialised.flags
                                                        |> Maybe.map
                                                            (\_ ->
                                                                if host == Nothing then
                                                                    "none"

                                                                else
                                                                    "echo"
                                                            )
                                                , flags = directives.flagsText
                                                , dropped = directives.dropped
                                                , checkNots = directives.checkNots
                                                , library = library
                                                }


{-| The test runner's echo host (runner/run.js, `launcher`): installed when the program has an
outgoing port `echoOut` and an incoming port `echoIn` and refers to both outside their declarations
(Elm/JS leaves an unreferenced port out of `app.ports`).
-}
echoHost : TestProgram -> Dict.Dict Int ( Bool, Ir.Payload ) -> Maybe ( String, String )
echoHost program ports =
    let
        allPorts =
            List.concatMap .ports program.modules

        defs =
            List.concatMap .defs program.modules

        referenced binder =
            List.any
                (\d ->
                    case d of
                        DFn f ->
                            anyExpr (refersTo binder) f.body

                        DPat _ x ->
                            anyExpr (refersTo binder) x
                )
                defs

        portIs name out =
            allPorts
                |> List.any
                    (\pd ->
                        pd.name == name && (Dict.get pd.binder ports |> Maybe.map Tuple.first) == Just out && referenced pd.binder
                    )
    in
    if portIs "echoOut" True && portIs "echoIn" False then
        Just ( "echoOut", "echoIn" )

    else
        Nothing


refersTo : Int -> Expr -> Bool
refersTo binder e =
    case e of
        EVar _ (Local id _) ->
            id == binder

        EVar _ (Foreign f) ->
            f.binder == binder

        _ ->
            False


mainSource : { project : String, name : String, defName : String } -> String -> Parsed -> ModuleSource
mainSource info source file =
    { name = info.name, path = mainPath info, source = source, file = file }


mainPath : { project : String, name : String, defName : String } -> String
mainPath info =
    "tests/" ++ info.project ++ "/src/" ++ info.name ++ ".elm"


{-| A stage of the pipeline, for the report of all refusals (step 0 of
plans/lean-full-definition.md).
-}
type Stage
    = StDirectives
    | StSize
    | StParse
    | StConvert
    | StInfer
    | StSpecialise


stageName : Stage -> String
stageName stage =
    case stage of
        StDirectives ->
            "directives"

        StSize ->
            "size"

        StParse ->
            "parse"

        StConvert ->
            "convert"

        StInfer ->
            "infer"

        StSpecialise ->
            "specialise"


type alias Found =
    { stage : Stage, reason : String, at : Maybe String, detail : Maybe String }


found : Stage -> String -> Found
found stage reason =
    { stage = stage, reason = reason, at = Nothing, detail = Nothing }


{-| Every refusal met when each is lifted in turn, in pipeline order; [] for a test that
translates. The first element, if any, is the refusal `translate` reports. A compile-error test
reports only its directive; parsing and inference stop the report (there is no tree, and
inference stops at its first error).
-}
translateAll : { project : String, name : String, defName : String } -> String -> Directives -> List Found
translateAll =
    translateAllWith (\_ -> Nothing)


translateAllWith : Lookup -> { project : String, name : String, defName : String } -> String -> Directives -> List Found
translateAllWith =
    translateAllIn Library.empty


{-| `translateAllWith` for a program that may name the values of the core library `lib`.
-}
translateAllIn : Library -> Lookup -> { project : String, name : String, defName : String } -> String -> Directives -> List Found
translateAllIn lib lookup info source directives =
    let
        fromDirectives =
            List.map (found StDirectives) directives.refusals

        size =
            (if String.length source > largeProgram then
                [ found StSize "construct:large-program" ]

             else
                []
            )
                ++ (if List.member info.name largeComputations then
                        [ found StSize "construct:large-computation" ]

                    else
                        []
                   )
    in
    if List.member "compile-error" directives.refusals then
        fromDirectives

    else if not (List.isEmpty size) then
        -- a test of a compiler's limits: its tree is too large for the converter's and the
        -- inference's recursion, so the report stops here, as translate does
        fromDirectives ++ size

    else
        fromDirectives
            ++ size
            ++ (case parseModule (mainPath info) source of
                    Err refusal ->
                        [ { stage = StParse, reason = refusal.reason, at = refusal.at, detail = refusal.detail } ]

                    Ok file0 ->
                        case resolve lookup (mainSource info source file0) of
                            Err refusal ->
                                -- as before eco's parser: a refusal while the modules are resolved
                                -- is reported at the converter's stage
                                [ { stage = StConvert, reason = refusal.reason, at = refusal.at, detail = refusal.detail } ]

                            Ok sources ->
                                afterResolution lib directives sources
               )


{-| The refusals from conversion on, for a program whose modules are resolved.
-}
afterResolution : Library -> Directives -> List ModuleSource -> List Found
afterResolution lib directives sources =
    let
        ( program, problems ) =
            Convert.convertProgram lib directives sources

        fromConvert =
            List.map
                (\p ->
                    { stage = StConvert
                    , reason = p.code
                    , at = Just (Region.startText p.at)
                    , detail = Nothing
                    }
                )
                problems
    in
    if List.any (\p -> String.startsWith "construct:large" p.code) problems then
        -- too large for inference's recursion, as for size above
        fromConvert

    else
        fromConvert
            ++ (case Infer.inferWith lib program of
                    Err message ->
                        if String.startsWith "unknown-type:" message || isReason message then
                            [ found StInfer message ]

                        else
                            [ { stage = StInfer, reason = "type", at = Nothing, detail = Just message } ]

                    Ok inferred ->
                        case Specialise.specialiseWith lib program inferred of
                            Err message ->
                                if String.startsWith "basis:" message then
                                    [ found StSpecialise message ]

                                else
                                    [ { stage = StSpecialise, reason = "number", at = Nothing, detail = Just message } ]

                            Ok _ ->
                                []
               )
