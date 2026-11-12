module Translate.Choices exposing (Choices, apply, decoder, path)

{-| The scheduler's choices for worker tests whose checks the default strategy does not meet
(plans/lean-full-definition/step-05-programs.md, translator change 6), read from
`definition/mechanisation/worker-choices.json`: for a test `"<project>/<Name>"`, the order of a
batch's leaves, the scheduler's fuel, and choices that override the default strategy at given
iterations. A choice is `"update"`, `"in"`, `"wake"`, `"stop"`, `{"proc": n}`, `{"out": "port"}`
or `{"wait": "<decimal>"}` (the decimal written exactly, as `jnum`). No test needs one today; the
file is `{}`.
-}

import Dict exposing (Dict)
import Json.Decode as Decode exposing (Decoder)
import Translate.Json as Json
import Translate.Literal exposing (leanString)


path : String
path =
    "definition/mechanisation/worker-choices.json"


{-| For each test, the Lean fields its worker test gains.
-}
type alias Choices =
    Dict String String


decoder : Decoder Choices
decoder =
    Decode.dict entry


entry : Decoder String
entry =
    Decode.map3
        (\leafOrder fuel overrides ->
            "  sched := { leafOrder := ."
                ++ Maybe.withDefault "reversed" leafOrder
                ++ ", overrides := ["
                ++ String.join ", " overrides
                ++ "] },\n"
                ++ (fuel |> Maybe.map (\n -> "  fuel := " ++ String.fromInt n ++ ",\n") |> Maybe.withDefault "")
        )
        (Decode.maybe (Decode.field "leafOrder" (Decode.string |> Decode.andThen leafOrderName)))
        (Decode.maybe (Decode.field "fuel" Decode.int))
        (Decode.maybe (Decode.field "overrides" (Decode.list override)) |> Decode.map (Maybe.withDefault []))


leafOrderName : String -> Decoder String
leafOrderName s =
    if s == "listed" || s == "reversed" then
        Decode.succeed s

    else
        Decode.fail ("leafOrder: " ++ s)


override : Decoder String
override =
    Decode.map2 (\at c -> "(" ++ String.fromInt at ++ ", " ++ c ++ ")")
        (Decode.field "at" Decode.int)
        (Decode.field "choice" choice)


choice : Decoder String
choice =
    Decode.oneOf
        [ Decode.string
            |> Decode.andThen
                (\s ->
                    case s of
                        "update" ->
                            Decode.succeed ".update"

                        "in" ->
                            Decode.succeed ".inn"

                        "wake" ->
                            Decode.succeed ".wake"

                        "stop" ->
                            Decode.succeed ".stop"

                        _ ->
                            Decode.fail ("choice: " ++ s)
                )
        , Decode.field "proc" Decode.int |> Decode.map (\n -> "(.proc " ++ String.fromInt n ++ ")")
        , Decode.field "out" Decode.string |> Decode.map (\p -> "(.out " ++ leanString p ++ ")")
        , Decode.field "wait" Decode.string
            |> Decode.andThen
                (\d ->
                    case Json.parse d of
                        Just (Json.JNum m e) ->
                            Decode.succeed ("(.wait (Eff.jnum (" ++ m ++ ") (" ++ String.fromInt e ++ ")))")

                        _ ->
                            Decode.fail ("wait: " ++ d)
                )
        ]


{-| The worker test's text with the fields of its choices, before its (empty) checks.
-}
apply : String -> String -> String
apply fields lean =
    String.replace "\n  checks := [] }" ("\n" ++ String.dropRight 1 fields ++ "\n  checks := [] }") lean
