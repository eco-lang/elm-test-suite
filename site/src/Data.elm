module Data exposing
    ( Check
    , CheckKind(..)
    , Compiler
    , Counts
    , Differing
    , Outcome
    , Project
    , ProjectSummary
    , Report
    , Status(..)
    , Test
    , TestRef
    , TestResult
    , TestRow
    , project
    , report
    , statusLabel
    , tag
    , test
    , testsByPlace
    , testsChecking
    )

{-| The results data `runner/site-data.js` writes under `data/`, and the backend tasks that read it.
-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import Dict
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
    , tags : List ProjectSummary
    , differing : List Differing
    }


type alias Outcome =
    { status : Status
    , reason : String
    }


{-| A test in the table of a project or a tag. `tags` are its tags but its project; `xfail` is the
reason, when the test is expected to fail (`-- XFAIL:`).
-}
type alias TestRow =
    { project : String
    , name : String
    , summary : String
    , compileError : Bool
    , tags : List String
    , outcomes : List Outcome
    , xfail : Maybe String
    }


{-| A project, or a tag: its name, description and tests.
-}
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
    , cached : Maybe String
    }


type alias Test =
    { project : String
    , name : String
    , doc : String
    , issues : List String
    , tags : List String
    , checks : List Check
    , source : String
    , results : List TestResult
    , xfail : Maybe String
    }


type CheckKind
    = Rule
    | Restriction
    | DerivedForm
    | Basis
    | Figure
    | Place


{-| A rule, restriction, derived form or entry of the initial basis of A Standard Definition of
Elm? that a test checks: the test has a tag that names it. `name` is the item's name without the
`df:`, `b:` or `fig:` of its tag; a figure is also found at `anchor` in the chapter `chapter`. A
`Place` is a section of a chapter: `name` is its title, and it is found at `anchor` in the chapter
`chapter`.
-}
type alias Check =
    { kind : CheckKind
    , name : String
    , chapter : String
    , anchor : String
    }


{-| A test that checks an item of the book, as the item's page lists it.
-}
type alias TestRef =
    { project : String
    , test : String
    , summary : String
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


{-| The tests with a tag (`-- TAGS:`), as a `Project`.
-}
tag : String -> BackendTask FatalError Project
tag name =
    load projectDecoder ("data/tags/" ++ name ++ ".json")


{-| The tests that check an item of the book, by its name.
-}
testsChecking : CheckKind -> String -> BackendTask FatalError (List TestRef)
testsChecking kind name =
    load
        (Decode.field
            (case kind of
                Rule ->
                    "rules"

                Restriction ->
                    "restrictions"

                DerivedForm ->
                    "derivedForms"

                Basis ->
                    "basis"

                Figure ->
                    "figures"

                Place ->
                    "places"
            )
            (Decode.dict (Decode.list testRefDecoder))
        )
        "data/checks.json"
        |> BackendTask.map (Dict.get name >> Maybe.withDefault [])


testRefDecoder : Decoder TestRef
testRefDecoder =
    Decode.map3 TestRef
        (Decode.field "project" Decode.string)
        (Decode.field "test" Decode.string)
        (Decode.field "summary" Decode.string)


checkDecoder : Decoder Check
checkDecoder =
    Decode.map4 Check
        (Decode.field "kind" Decode.string
            |> Decode.map
                (\k ->
                    case k of
                        "rule" ->
                            Rule

                        "derived-form" ->
                            DerivedForm

                        "basis" ->
                            Basis

                        "figure" ->
                            Figure

                        "section" ->
                            Place

                        _ ->
                            Restriction
                )
        )
        (Decode.field "name" Decode.string)
        (Decode.oneOf [ Decode.field "chapter" Decode.string, Decode.succeed "" ])
        (Decode.oneOf [ Decode.field "anchor" Decode.string, Decode.succeed "" ])


{-| The tests that check the figures and sections of the book, by their anchors in their chapters.
-}
testsByPlace : BackendTask FatalError (Dict.Dict String (List TestRef))
testsByPlace =
    load (Decode.field "places" (Decode.dict (Decode.list testRefDecoder))) "data/checks.json"


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


andMap : Decoder a -> Decoder (a -> b) -> Decoder b
andMap =
    Decode.map2 (|>)


summaryDecoder : Decoder ProjectSummary
summaryDecoder =
    Decode.map4 ProjectSummary
        (Decode.field "name" Decode.string)
        (Decode.field "description" Decode.string)
        (Decode.field "total" Decode.int)
        (Decode.field "counts" (Decode.list countsDecoder))


reportDecoder : Decoder Report
reportDecoder =
    Decode.succeed Report
        |> andMap (Decode.field "generated" Decode.string)
        |> andMap (Decode.field "commit" Decode.string)
        |> andMap (Decode.field "repository" Decode.string)
        |> andMap (Decode.field "runUrl" Decode.string)
        |> andMap (Decode.field "node" Decode.string)
        |> andMap (Decode.field "compilers" (Decode.list compilerDecoder))
        |> andMap (Decode.field "projects" (Decode.list summaryDecoder))
        |> andMap (Decode.field "tags" (Decode.list summaryDecoder))
        |> andMap
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
                (Decode.map7 TestRow
                    (Decode.field "project" Decode.string)
                    (Decode.field "name" Decode.string)
                    (Decode.field "summary" Decode.string)
                    (Decode.field "compileError" Decode.bool)
                    (Decode.field "tags" (Decode.list Decode.string))
                    (Decode.field "outcomes"
                        (Decode.list
                            (Decode.map2 Outcome
                                (Decode.field "status" statusDecoder)
                                (Decode.field "reason" Decode.string)
                            )
                        )
                    )
                    xfailDecoder
                )
            )
        )


{-| The reason a test is expected to fail, if it is.
-}
xfailDecoder : Decoder (Maybe String)
xfailDecoder =
    Decode.oneOf [ Decode.field "xfail" (Decode.nullable Decode.string), Decode.succeed Nothing ]


testDecoder : Decoder Test
testDecoder =
    Decode.map8 Test
        (Decode.field "project" Decode.string)
        (Decode.field "name" Decode.string)
        (Decode.field "doc" Decode.string)
        (Decode.field "issues" (Decode.list Decode.string))
        (Decode.field "tags" (Decode.list Decode.string))
        (Decode.field "checks" (Decode.list checkDecoder))
        (Decode.field "source" Decode.string)
        (Decode.field "results"
            (Decode.list
                (Decode.map6 TestResult
                    (Decode.field "compiler" Decode.string)
                    (Decode.field "status" statusDecoder)
                    (Decode.field "message" Decode.string)
                    (Decode.field "output" Decode.string)
                    (Decode.field "ms" (Decode.nullable Decode.int))
                    -- The time a result from the result cache was produced (absent in older data).
                    (Decode.oneOf [ Decode.field "cached" (Decode.nullable Decode.string), Decode.succeed Nothing ])
                )
            )
        )
        |> andMap xfailDecoder
