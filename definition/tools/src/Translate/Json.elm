module Translate.Json exposing (Json(..), parse, toLean)

{-| A parser of RFC 8259 JSON text, for the flags of a worker test (`-- FLAGS:`), that keeps every
number exact: a number is its digits and exponent, written in Lean as `jnum m e` (m × 10^e), never
converted to an Elm `Float` (binary64 is inexact for large integers and most decimals). `-0` is
`jnum 0 0`: a JSON number has no sign apart from its value (A88). Objects are written through
`BVal.mkObj`, which sorts the keys and keeps the last value of a repeated key, as a JSON parser
reads it.
-}

import Translate.Literal exposing (leanString)


type Json
    = JNull
    | JTrue
    | JFalse
      -- mantissa digits (with sign), exponent
    | JNum String Int
    | JStr String
    | JArr (List Json)
    | JObj (List ( String, Json ))


parse : String -> Maybe Json
parse text =
    case value (String.toList text |> skipWs) of
        Just ( j, rest ) ->
            if List.isEmpty (skipWs rest) then
                Just j

            else
                Nothing

        Nothing ->
            Nothing


skipWs : List Char -> List Char
skipWs cs =
    case cs of
        c :: rest ->
            if c == ' ' || c == '\t' || c == '\n' || c == '\u{000D}' then
                skipWs rest

            else
                cs

        [] ->
            []


value : List Char -> Maybe ( Json, List Char )
value cs =
    case skipWs cs of
        'n' :: 'u' :: 'l' :: 'l' :: rest ->
            Just ( JNull, rest )

        't' :: 'r' :: 'u' :: 'e' :: rest ->
            Just ( JTrue, rest )

        'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest ->
            Just ( JFalse, rest )

        '"' :: rest ->
            string rest [] |> Maybe.map (\( s, r ) -> ( JStr s, r ))

        '[' :: rest ->
            case skipWs rest of
                ']' :: r ->
                    Just ( JArr [], r )

                _ ->
                    elements rest []

        '{' :: rest ->
            case skipWs rest of
                '}' :: r ->
                    Just ( JObj [], r )

                _ ->
                    members rest []

        c :: _ ->
            if c == '-' || Char.isDigit c then
                number (skipWs cs)

            else
                Nothing

        [] ->
            Nothing


elements : List Char -> List Json -> Maybe ( Json, List Char )
elements cs acc =
    value cs
        |> Maybe.andThen
            (\( j, rest ) ->
                case skipWs rest of
                    ',' :: r ->
                        elements r (acc ++ [ j ])

                    ']' :: r ->
                        Just ( JArr (acc ++ [ j ]), r )

                    _ ->
                        Nothing
            )


members : List Char -> List ( String, Json ) -> Maybe ( Json, List Char )
members cs acc =
    case skipWs cs of
        '"' :: rest ->
            string rest []
                |> Maybe.andThen
                    (\( k, r1 ) ->
                        case skipWs r1 of
                            ':' :: r2 ->
                                value r2
                                    |> Maybe.andThen
                                        (\( j, r3 ) ->
                                            case skipWs r3 of
                                                ',' :: r4 ->
                                                    members r4 (acc ++ [ ( k, j ) ])

                                                '}' :: r4 ->
                                                    Just ( JObj (acc ++ [ ( k, j ) ]), r4 )

                                                _ ->
                                                    Nothing
                                        )

                            _ ->
                                Nothing
                    )

        _ ->
            Nothing


string : List Char -> List Char -> Maybe ( String, List Char )
string cs acc =
    case cs of
        '"' :: rest ->
            Just ( String.fromList (List.reverse acc), rest )

        '\\' :: e :: rest ->
            case e of
                'n' ->
                    string rest ('\n' :: acc)

                't' ->
                    string rest ('\t' :: acc)

                'r' ->
                    string rest ('\u{000D}' :: acc)

                'b' ->
                    string rest ('\u{0008}' :: acc)

                'f' ->
                    string rest ('\u{000C}' :: acc)

                '/' ->
                    string rest ('/' :: acc)

                '\\' ->
                    string rest ('\\' :: acc)

                '"' ->
                    string rest ('"' :: acc)

                'u' ->
                    case rest of
                        a :: b :: c :: d :: r ->
                            case hex [ a, b, c, d ] of
                                Just n ->
                                    string r (Char.fromCode n :: acc)

                                Nothing ->
                                    Nothing

                        _ ->
                            Nothing

                _ ->
                    Nothing

        c :: rest ->
            string rest (c :: acc)

        [] ->
            Nothing


hex : List Char -> Maybe Int
hex =
    List.foldl
        (\c acc ->
            acc
                |> Maybe.andThen
                    (\n ->
                        let
                            d =
                                if Char.isDigit c then
                                    Just (Char.toCode c - 48)

                                else if c >= 'a' && c <= 'f' then
                                    Just (Char.toCode c - 87)

                                else if c >= 'A' && c <= 'F' then
                                    Just (Char.toCode c - 55)

                                else
                                    Nothing
                        in
                        Maybe.map (\x -> n * 16 + x) d
                    )
        )
        (Just 0)


{-| A number: sign, integer digits, fraction digits, exponent; kept as mantissa digits and a
power of ten.
-}
number : List Char -> Maybe ( Json, List Char )
number cs =
    let
        ( neg, r0 ) =
            case cs of
                '-' :: r ->
                    ( True, r )

                _ ->
                    ( False, cs )

        ( intDigits, r1 ) =
            span Char.isDigit r0

        ( fracDigits, r2 ) =
            case r1 of
                '.' :: r ->
                    span Char.isDigit r

                _ ->
                    ( [], r1 )

        ( expo, r3 ) =
            case r2 of
                e :: r ->
                    if e == 'e' || e == 'E' then
                        let
                            ( eneg, re ) =
                                case r of
                                    '-' :: x ->
                                        ( True, x )

                                    '+' :: x ->
                                        ( False, x )

                                    _ ->
                                        ( False, r )

                            ( eds, rr ) =
                                span Char.isDigit re
                        in
                        ( Maybe.map
                            (\n ->
                                if eneg then
                                    -n

                                else
                                    n
                            )
                            (String.toInt (String.fromList eds))
                        , rr
                        )

                    else
                        ( Just 0, r2 )

                [] ->
                    ( Just 0, r2 )

        digits =
            String.fromList (intDigits ++ fracDigits)
                |> dropLeadingZeros
    in
    if List.isEmpty intDigits then
        Nothing

    else
        case expo of
            Just e ->
                Just
                    ( JNum
                        (if neg && digits /= "0" then
                            "-" ++ digits

                         else
                            digits
                        )
                        (e - List.length fracDigits)
                    , r3
                    )

            Nothing ->
                Nothing


span : (Char -> Bool) -> List Char -> ( List Char, List Char )
span p cs =
    case cs of
        c :: rest ->
            if p c then
                let
                    ( a, b ) =
                        span p rest
                in
                ( c :: a, b )

            else
                ( [], cs )

        [] ->
            ( [], [] )


dropLeadingZeros : String -> String
dropLeadingZeros s =
    let
        t =
            String.toList s |> dropWhile (\c -> c == '0') |> String.fromList
    in
    if String.isEmpty t then
        "0"

    else
        t


dropWhile : (a -> Bool) -> List a -> List a
dropWhile p xs =
    case xs of
        x :: rest ->
            if p x then
                dropWhile p rest

            else
                xs

        [] ->
            []


{-| The boundary value as a Lean term (Eff/Boundary.lean).
-}
toLean : Json -> String
toLean j =
    case j of
        JNull ->
            ".null"

        JTrue ->
            ".tru"

        JFalse ->
            ".fls"

        JNum m e ->
            "(.num (Eff.jnum (" ++ m ++ ") (" ++ String.fromInt e ++ ")))"

        JStr s ->
            "(.str " ++ leanString s ++ ")"

        JArr js ->
            "(Eff.BVal.array [" ++ String.join ", " (List.map toLean js) ++ "])"

        JObj kvs ->
            "(Eff.BVal.mkObj [" ++ String.join ", " (List.map (\( k, v ) -> "(" ++ leanString k ++ ", " ++ toLean v ++ ")") kvs) ++ "])"
