module Translate.Pipeline exposing (Outcome(..), Refusal, translate)

{-| One test, from source to Lean or to the reason it is not translated: directives, parsing,
conversion (names, fragment, checks), inference, number specialisation, printing.
-}

import Elm.Parser
import Translate.Convert as Convert
import Translate.Directives as Directives exposing (Directives)
import Translate.Infer as Infer
import Translate.Specialise as Specialise
import Translate.ToLean as ToLean


type alias Refusal =
    { reason : String, at : Maybe String, detail : Maybe String }


type Outcome
    = Translated { lean : String, checks : Int }
    | Refused Refusal


refuse : String -> Outcome
refuse reason =
    Refused { reason = reason, at = Nothing, detail = Nothing }


translate : { project : String, name : String, defName : String } -> String -> Directives -> Outcome
translate info source directives =
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
                parseAndTranslate info source directives


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
    ]


parseAndTranslate : { project : String, name : String, defName : String } -> String -> Directives -> Outcome
parseAndTranslate info source directives =
            case Elm.Parser.parseToFile source of
                Err _ ->
                    refuse "parse"

                Ok file ->
                    case Convert.convert source directives file of
                        Err p ->
                            Refused
                                { reason = p.code
                                , at = Just (String.fromInt p.at.start.row ++ ":" ++ String.fromInt p.at.start.column)
                                , detail = Nothing
                                }

                        Ok program ->
                            case Infer.infer program of
                                Err message ->
                                    Refused { reason = "type", at = Nothing, detail = Just message }

                                Ok inferred ->
                                    case Specialise.specialise program inferred of
                                        Err message ->
                                            if String.startsWith "basis:" message then
                                                Refused { reason = message, at = Nothing, detail = Nothing }

                                            else
                                                Refused { reason = "number", at = Nothing, detail = Just message }

                                        Ok specialised ->
                                            Translated
                                                { lean = ToLean.programDef info specialised.program specialised.kinds specialised.native
                                                , checks = List.length specialised.program.checks
                                                }
