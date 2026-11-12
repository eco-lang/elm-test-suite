module Translate.Directives exposing (Directives, dropCheckNots, read)

{-| The directives of a test, read from its source text (they are comments, which the parser drops):
its tags, its CHECK-family lines in order, its exit status, and whether it is refused because of a
directive (plans/elm-to-lean-translator.md, B.2; plans/lean-full-definition/step-03-module-form.md).
-}

import Translate.Ir exposing (CheckLine, LineKind(..))
import Translate.Json as Json exposing (Json)


type alias Directives =
    { tags : List String
    , helper : Bool
    , lines : List CheckLine
    , meaning : Bool

    -- the flags of a worker (`-- FLAGS:`), exactly; absent flags are null (A72)
    , flags : Maybe Json
    , flagsText : Maybe String

    -- the CHECK-NOT lines dropped by `dropCheckNots`, with the reason
    , dropped : List String

    -- the patterns of the CHECK-NOT lines proved by hand (`checkNotProofs`, plan step 6)
    , checkNots : List String
    , refusal : Maybe String
    , refusals : List String
    }


prefix : String -> String -> Maybe String
prefix p line =
    if String.startsWith p line then
        Just (String.dropLeft (String.length p) line)

    else
        Nothing


read : String -> Directives
read source =
    let
        lines =
            String.lines source |> List.filter (String.startsWith "-- ")

        tags =
            lines
                |> List.filterMap (prefix "-- TAGS:")
                |> List.concatMap (String.split ",")
                |> List.map String.trim
                |> List.filter (not << String.isEmpty)

        exit =
            lines |> List.filterMap (prefix "-- EXIT:") |> List.map String.trim |> List.head

        has p =
            List.any (String.startsWith p) lines

        refusedBy =
            [ ( "-- COMPILE-ERROR:", "compile-error" )
            , ( "-- STDIN:", "effects" )
            , ( "-- STDIN-DELAY-MS:", "effects" )
            , ( "-- ENV:", "effects" )
            , ( "-- UNSETENV:", "effects" )
            , ( "-- CHECK-LABEL:", "checks:directive:CHECK-LABEL" )
            ]
                |> List.filter (\( p, _ ) -> has p)
                |> List.map Tuple.second

        -- the CHECK family, in the order written; CHECK-DAG is read as CHECK (D9)
        lineOf l =
            [ ( "-- CHECK-NOT:", LNot ), ( "-- CHECK-NEXT:", LNext ), ( "-- CHECK-SAME:", LSame ), ( "-- CHECK-DAG:", LCheck ), ( "-- CHECK:", LCheck ) ]
                |> List.filterMap (\( p, k ) -> prefix p l |> Maybe.map (\t -> { kind = k, text = String.trim t }))
                |> List.head

        checkLines =
            List.filterMap lineOf lines |> List.filter (\l -> not (String.isEmpty l.text))

        notLines =
            List.filter (\l -> l.kind == LNot) checkLines

        notRefusal =
            if not (List.isEmpty notLines) && exit /= Just "1" then
                [ "checks:check-not" ]

            else
                []

        exitRefusal =
            case exit of
                Nothing ->
                    []

                Just "0" ->
                    []

                Just "1" ->
                    if List.isEmpty notLines then
                        [ "checks:exit" ]

                    else
                        []

                Just _ ->
                    [ "checks:exit" ]

        flagsText =
            lines |> List.filterMap (prefix "-- FLAGS:") |> List.map String.trim |> List.head

        flags =
            flagsText |> Maybe.andThen Json.parse

        flagsRefusal =
            case ( flagsText, flags ) of
                ( Just _, Nothing ) ->
                    [ "construct:flags" ]

                _ ->
                    []

        problems =
            refusedBy ++ notRefusal ++ exitRefusal ++ flagsRefusal
    in
    { tags = tags
    , helper = has "-- HELPER:"
    , lines = checkLines
    , meaning = exit /= Just "1"
    , flags = flags
    , flagsText = flagsText
    , dropped = []
    , checkNots = []
    , refusal = List.head problems
    , refusals = problems
    }


{-| Tests whose CHECK-NOT lines the book does not require, with the reason: their positive checks
are stated and the CHECK-NOT lines are dropped (plan step 5).
-}
checkNotsNotRequired : List ( String, String )
checkNotsNotRequired =
    [ ( "StandardA81SleepBeyond32BitsTest", "finding T1: r:p-wait lets the long sleep end before the kill; not required by the book, theorem t1_a81_long_sleep_may_end" ) ]


{-| Drop the CHECK-NOT lines of a test the list names, and the refusal they caused. -}
dropCheckNots : String -> Directives -> Directives
dropCheckNots name d =
    case List.filter (\( n, _ ) -> n == name) checkNotsNotRequired of
        ( _, reason ) :: _ ->
            dropAll reason d

        [] ->
            if List.member name checkNotProofs then
                let
                    proved =
                        dropAll "" d
                in
                { proved
                    | dropped = []
                    , checkNots = d.lines |> List.filter (\l -> l.kind == LNot) |> List.map .text
                }

            else
                d


{-| Tests whose CHECK-NOT lines are proved by hand, as statements about every execution the book
allows under the test's host (plan step 6, `Prog/Inv/<Test>.lean`, theorem `checkNot`).
-}
checkNotProofs : List String
checkNotProofs =
    [ "TaskOnErrorSucceedTest", "PortIncomingRejectTest", "StandardA88PortNonFiniteTest" ]


dropAll : String -> Directives -> Directives
dropAll reason d =
    let
        problems =
            List.filter (\p -> p /= "checks:check-not") d.refusals
    in
    { d
        | lines = List.filter (\l -> l.kind /= LNot) d.lines
        , dropped = d.lines |> List.filter (\l -> l.kind == LNot) |> List.map (\l -> "CHECK-NOT: " ++ l.text ++ " (" ++ reason ++ ")")
        , refusal = List.head problems
        , refusals = problems
    }
