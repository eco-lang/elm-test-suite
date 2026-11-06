module Data exposing
    ( Compiler
    , Counts
    , Differing
    , Outcome
    , Project
    , ProjectSummary
    , Report
    , Status(..)
    , Test
    , TestResult
    , TestRow
    , project
    , report
    , statusLabel
    , test
    )

{-| The results data `runner/site-data.js` writes under `data/`, and the backend tasks that read it.
-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import FatalError exposing (FatalError)
import Json.Decode as Decode exposing (Decoder)


type Status
    = Pass
    | Fail
    | Skip
    | Missing


statusLabel : Status -> String
statusLabel status =
    case status of
        Pass ->
            "pass"

        Fail ->
            "fail"

        Skip ->
            "skip"

        Missing ->
            "missing"


type alias Counts =
    { pass : Int
    , fail : Int
    , skip : Int
    }


type alias Compiler =
    { name : String
    , version : String
    , description : String
    , target : String
    , counts : Counts
    }


type alias ProjectSummary =
    { name : String
    , description : String
    , total : Int
    , counts : List Counts
    }


type alias Differing =
    { project : String
    , test : String
    , outcomes : List Status
    }


type alias Report =
    { generated : String
    , commit : String
    , repository : String
    , runUrl : String
    , node : String
    , compilers : List Compiler
    , projects : List ProjectSummary
    , differing : List Differing
    }


type alias Outcome =
    { status : Status
    , reason : String
    }


type alias TestRow =
    { name : String
    , summary : String
    , compileError : Bool
    , outcomes : List Outcome
    }


type alias Project =
    { name : String
    , description : String
    , tests : List TestRow
    }


type alias TestResult =
    { compiler : String
    , status : Status
    , message : String
    , output : String
    , ms : Maybe Int
    }


type alias Test =
    { project : String
    , name : String
    , doc : String
    , issues : List String
    , source : String
    , results : List TestResult
    }



-- LOADING


load : Decoder a -> String -> BackendTask FatalError a
load decoder path =
    BackendTask.File.jsonFile decoder path
        |> BackendTask.allowFatal


report : BackendTask FatalError Report
report =
    load reportDecoder "data/report.json"


project : String -> BackendTask FatalError Project
project name =
    load projectDecoder ("data/projects/" ++ name ++ ".json")


test : String -> String -> BackendTask FatalError Test
test projectName testName =
    load testDecoder ("data/tests/" ++ projectName ++ "/" ++ testName ++ ".json")



-- DECODERS


statusDecoder : Decoder Status
statusDecoder =
    Decode.string
        |> Decode.map
            (\s ->
                case s of
                    "pass" ->
                        Pass

                    "fail" ->
                        Fail

                    "skip" ->
                        Skip

                    _ ->
                        Missing
            )


countsDecoder : Decoder Counts
countsDecoder =
    Decode.map3 Counts
        (Decode.field "pass" Decode.int)
        (Decode.field "fail" Decode.int)
        (Decode.field "skip" Decode.int)


compilerDecoder : Decoder Compiler
compilerDecoder =
    Decode.map5 Compiler
        (Decode.field "name" Decode.string)
        (Decode.field "version" Decode.string)
        (Decode.field "description" Decode.string)
        (Decode.field "target" Decode.string)
        countsDecoder


reportDecoder : Decoder Report
reportDecoder =
    Decode.map8 Report
        (Decode.field "generated" Decode.string)
        (Decode.field "commit" Decode.string)
        (Decode.field "repository" Decode.string)
        (Decode.field "runUrl" Decode.string)
        (Decode.field "node" Decode.string)
        (Decode.field "compilers" (Decode.list compilerDecoder))
        (Decode.field "projects"
            (Decode.list
                (Decode.map4 ProjectSummary
                    (Decode.field "name" Decode.string)
                    (Decode.field "description" Decode.string)
                    (Decode.field "total" Decode.int)
                    (Decode.field "counts" (Decode.list countsDecoder))
                )
            )
        )
        (Decode.field "differing"
            (Decode.list
                (Decode.map3 Differing
                    (Decode.field "project" Decode.string)
                    (Decode.field "test" Decode.string)
                    (Decode.field "outcomes" (Decode.list statusDecoder))
                )
            )
        )


projectDecoder : Decoder Project
projectDecoder =
    Decode.map3 Project
        (Decode.field "name" Decode.string)
        (Decode.field "description" Decode.string)
        (Decode.field "tests"
            (Decode.list
                (Decode.map4 TestRow
                    (Decode.field "name" Decode.string)
                    (Decode.field "summary" Decode.string)
                    (Decode.field "compileError" Decode.bool)
                    (Decode.field "outcomes"
                        (Decode.list
                            (Decode.map2 Outcome
                                (Decode.field "status" statusDecoder)
                                (Decode.field "reason" Decode.string)
                            )
                        )
                    )
                )
            )
        )


testDecoder : Decoder Test
testDecoder =
    Decode.map6 Test
        (Decode.field "project" Decode.string)
        (Decode.field "name" Decode.string)
        (Decode.field "doc" Decode.string)
        (Decode.field "issues" (Decode.list Decode.string))
        (Decode.field "source" Decode.string)
        (Decode.field "results"
            (Decode.list
                (Decode.map5 TestResult
                    (Decode.field "compiler" Decode.string)
                    (Decode.field "status" statusDecoder)
                    (Decode.field "message" Decode.string)
                    (Decode.field "output" Decode.string)
                    (Decode.field "ms" (Decode.nullable Decode.int))
                )
            )
        )
