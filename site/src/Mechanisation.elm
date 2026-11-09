module Mechanisation exposing
    ( Generated
    , GeneratedCheck
    , Index
    , Method(..)
    , Proof
    , ProofLink
    , ProofSummary
    , Tactic
    , Translation
    , TranslatedCheck
    , generated
    , generatedSlug
    , index
    , methodName
    , proof
    , translation
    )

{-| The Lean proofs of the mechanisation of A Standard Definition of Elm?, as
`runner/mechanisation-data.js` writes them under `data-standard/mechanisation/`: the theorems read
from the Lean sources, and the theorems `kc_0`, `kc_1`, ... that the command `#kernel_checks`
generates at compile time, one per check of a test program.
-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import FatalError exposing (FatalError)
import Json.Decode as Decode exposing (Decoder)



-- TYPES


{-| How a theorem is proved: by the kernel evaluating a decision procedure (`decide +kernel`), by
`native_decide` (which trusts the compiled evaluator), by tactics, or by a term.
-}
type Method
    = Kernel
    | NativeDecide
    | Tactics
    | Term


type alias Index =
    { lean : String
    , rules : Int
    , checks : Maybe { checks : Int, agree : Int, diverge : Int }
    , files : List { path : String, description : String }
    , theorems : List ProofSummary
    , generatedCount : Int
    }


type alias ProofSummary =
    { name : String
    , slug : String
    , file : String
    , line : Int
    , section : Maybe String
    , summary : String
    , method : Method
    }


type alias ProofLink =
    { name : String
    , slug : String
    }


type alias Tactic =
    { name : String
    , file : String
    , line : Int
    , doc : String
    , source : String
    }


type alias Proof =
    { summary : ProofSummary
    , doc : String
    , fileDescription : String
    , statement : String
    , proof : String
    , uses : List ProofLink
    , usedBy : List ProofLink
    , rules : List String
    , rulings : List String
    , tactics : List Tactic
    , prev : Maybe ProofLink
    , next : Maybe ProofLink
    }


type alias GeneratedCheck =
    { name : String
    , program : String
    , project : Maybe String
    , label : String
    , expected : String
    , kind : String
    }


type alias Generated =
    { count : Int
    , source : Maybe { file : String, line : Int, text : String }
    , groups : List { key : String, title : String, programs : Int, checks : Int, generated : Int }
    , skipped : { divergence : Int, float : Int, value : Int }
    , checks : List GeneratedCheck
    }


{-| A test program as the mechanisation's examples translate it: the Lean definition, and what became
of each of its checks. `checkLine` is the test's CHECK value now, which the translation's `expected`
should still be.
-}
type alias Translation =
    { name : String
    , project : String
    , def : String
    , file : String
    , line : Int
    , doc : String
    , group : String
    , source : String
    , checks : List TranslatedCheck
    }


type alias TranslatedCheck =
    { label : String
    , expected : String
    , checkLine : Maybe String
    , definition : String
    , status : String
    , theorem : Maybe String
    , skipped : Maybe String
    }


{-| The address of the page of the generated theorems, beside the pages of the theorems.
-}
generatedSlug : String
generatedSlug =
    "kc"


methodName : Method -> String
methodName method =
    case method of
        Kernel ->
            "kernel-checked (decide +kernel)"

        NativeDecide ->
            "native_decide (trusts the compiled evaluator)"

        Tactics ->
            "tactic proof"

        Term ->
            "term proof"



-- LOADING


load : Decoder a -> String -> BackendTask FatalError a
load decoder path =
    BackendTask.File.jsonFile decoder path
        |> BackendTask.allowFatal


index : BackendTask FatalError Index
index =
    load indexDecoder "data-standard/mechanisation/index.json"


proof : String -> BackendTask FatalError Proof
proof slug =
    load proofDecoder ("data-standard/mechanisation/proofs/" ++ slug ++ ".json")


generated : BackendTask FatalError Generated
generated =
    load generatedDecoder ("data-standard/mechanisation/proofs/" ++ generatedSlug ++ ".json")


{-| The Lean translation of a test program, if the mechanisation's examples include it.
-}
translation : String -> String -> BackendTask FatalError (Maybe Translation)
translation project test =
    load (Decode.list Decode.string) "data-standard/mechanisation/translations/index.json"
        |> BackendTask.andThen
            (\translated ->
                if List.member (project ++ "/" ++ test) translated then
                    load translationDecoder ("data-standard/mechanisation/translations/" ++ project ++ "/" ++ test ++ ".json")
                        |> BackendTask.map Just

                else
                    BackendTask.succeed Nothing
            )



-- DECODERS


andMap : Decoder a -> Decoder (a -> b) -> Decoder b
andMap =
    Decode.map2 (|>)


methodDecoder : Decoder Method
methodDecoder =
    Decode.string
        |> Decode.map
            (\s ->
                case s of
                    "kernel" ->
                        Kernel

                    "native_decide" ->
                        NativeDecide

                    "tactics" ->
                        Tactics

                    _ ->
                        Term
            )


indexDecoder : Decoder Index
indexDecoder =
    Decode.succeed Index
        |> andMap (Decode.field "lean" Decode.string)
        |> andMap (Decode.field "rules" Decode.int)
        |> andMap
            (Decode.field "checks"
                (Decode.nullable
                    (Decode.map3 (\c a d -> { checks = c, agree = a, diverge = d })
                        (Decode.field "checks" Decode.int)
                        (Decode.field "agree" Decode.int)
                        (Decode.field "diverge" Decode.int)
                    )
                )
            )
        |> andMap
            (Decode.field "files"
                (Decode.list
                    (Decode.map2 (\p d -> { path = p, description = d })
                        (Decode.field "path" Decode.string)
                        (Decode.field "description" Decode.string)
                    )
                )
            )
        |> andMap (Decode.field "theorems" (Decode.list summaryDecoder))
        |> andMap (Decode.at [ "generated", "count" ] Decode.int)


summaryDecoder : Decoder ProofSummary
summaryDecoder =
    Decode.succeed ProofSummary
        |> andMap (Decode.field "name" Decode.string)
        |> andMap (Decode.field "slug" Decode.string)
        |> andMap (Decode.field "file" Decode.string)
        |> andMap (Decode.field "line" Decode.int)
        |> andMap (Decode.field "section" (Decode.nullable Decode.string))
        |> andMap (Decode.field "summary" Decode.string)
        |> andMap (Decode.field "method" methodDecoder)


linkDecoder : Decoder ProofLink
linkDecoder =
    Decode.map2 ProofLink
        (Decode.field "name" Decode.string)
        (Decode.field "slug" Decode.string)


tacticDecoder : Decoder Tactic
tacticDecoder =
    Decode.map5 Tactic
        (Decode.field "name" Decode.string)
        (Decode.field "file" Decode.string)
        (Decode.field "line" Decode.int)
        (Decode.field "doc" Decode.string)
        (Decode.field "source" Decode.string)


proofDecoder : Decoder Proof
proofDecoder =
    Decode.succeed Proof
        |> andMap summaryDecoder
        |> andMap (Decode.field "doc" Decode.string)
        |> andMap (Decode.field "fileDescription" Decode.string)
        |> andMap (Decode.field "statement" Decode.string)
        |> andMap (Decode.field "proof" Decode.string)
        |> andMap (Decode.field "uses" (Decode.list linkDecoder))
        |> andMap (Decode.field "usedBy" (Decode.list linkDecoder))
        |> andMap (Decode.field "rules" (Decode.list Decode.string))
        |> andMap (Decode.field "rulings" (Decode.list Decode.string))
        |> andMap (Decode.field "tactics" (Decode.list tacticDecoder))
        |> andMap (Decode.field "prev" (Decode.nullable linkDecoder))
        |> andMap (Decode.field "next" (Decode.nullable linkDecoder))


generatedDecoder : Decoder Generated
generatedDecoder =
    Decode.map5 Generated
        (Decode.field "count" Decode.int)
        (Decode.field "source"
            (Decode.nullable
                (Decode.map3 (\f l t -> { file = f, line = l, text = t })
                    (Decode.field "file" Decode.string)
                    (Decode.field "line" Decode.int)
                    (Decode.field "text" Decode.string)
                )
            )
        )
        (Decode.field "groups"
            (Decode.list
                (Decode.map5 (\k t p c g -> { key = k, title = t, programs = p, checks = c, generated = g })
                    (Decode.field "key" Decode.string)
                    (Decode.field "title" Decode.string)
                    (Decode.field "programs" Decode.int)
                    (Decode.field "checks" Decode.int)
                    (Decode.field "generated" Decode.int)
                )
            )
        )
        (Decode.field "skipped"
            (Decode.map3 (\d f v -> { divergence = d, float = f, value = v })
                (Decode.field "divergence" Decode.int)
                (Decode.field "float" Decode.int)
                (Decode.field "value" Decode.int)
            )
        )
        (Decode.field "checks"
            (Decode.list
                (Decode.succeed GeneratedCheck
                    |> andMap (Decode.field "name" Decode.string)
                    |> andMap (Decode.field "program" Decode.string)
                    |> andMap (Decode.field "project" (Decode.nullable Decode.string))
                    |> andMap (Decode.field "label" Decode.string)
                    |> andMap (Decode.field "expected" Decode.string)
                    |> andMap (Decode.field "kind" Decode.string)
                )
            )
        )


translationDecoder : Decoder Translation
translationDecoder =
    Decode.succeed Translation
        |> andMap (Decode.field "name" Decode.string)
        |> andMap (Decode.field "project" Decode.string)
        |> andMap (Decode.field "def" Decode.string)
        |> andMap (Decode.field "file" Decode.string)
        |> andMap (Decode.field "line" Decode.int)
        |> andMap (Decode.field "doc" Decode.string)
        |> andMap (Decode.field "group" Decode.string)
        |> andMap (Decode.field "source" Decode.string)
        |> andMap
            (Decode.field "checks"
                (Decode.list
                    (Decode.succeed TranslatedCheck
                        |> andMap (Decode.field "label" Decode.string)
                        |> andMap (Decode.field "expected" Decode.string)
                        |> andMap (Decode.field "checkLine" (Decode.nullable Decode.string))
                        |> andMap (Decode.field "definition" Decode.string)
                        |> andMap (Decode.field "status" Decode.string)
                        |> andMap (Decode.field "theorem" (Decode.nullable Decode.string))
                        |> andMap (Decode.field "skipped" (Decode.nullable Decode.string))
                    )
                )
            )
