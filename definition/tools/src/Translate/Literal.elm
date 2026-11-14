module Translate.Literal exposing
    ( decimalOfHex
    , floatOf
    , leanChar
    , leanString
    , normaliseDecimal
    , textAt
    )

{-| Literals from the source text: eco's parser holds integer and float literals as JavaScript numbers
beside their text, and those lose precision beyond 2^53, so the translator reads each literal's text
from the source by its region and works with the digits. Also: escaping for Lean string and char
literals.
-}

import Translate.Region exposing (Region)


{-| The text of a region of the source (rows and columns are 1-based, the end just past the last
character), across lines. Columns count characters (code points), and `String.slice` UTF-16 code
units, so each line is cut as a list of characters: an astral character earlier on the line would
otherwise shift the cut.
-}
textAt : String -> Region -> String
textAt source range =
    String.lines source
        |> List.drop (range.start.row - 1)
        |> List.take (range.end.row - range.start.row + 1)
        |> List.indexedMap
            (\i line ->
                let
                    chars =
                        String.toList line

                    upToEnd =
                        if i == range.end.row - range.start.row then
                            List.take (range.end.column - 1) chars

                        else
                            chars
                in
                (if i == 0 then
                    List.drop (range.start.column - 1) upToEnd

                 else
                    upToEnd
                )
                    |> String.fromList
            )
        |> String.join "\n"


normaliseDecimal : String -> String
normaliseDecimal digits =
    let
        trimmed =
            String.toList digits |> dropWhile ((==) '0') |> String.fromList
    in
    if String.isEmpty trimmed then
        "0"

    else
        trimmed


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


{-| `0xFF` -> "255", by arithmetic on decimal digits (least significant first), so that any size is
exact.
-}
decimalOfHex : String -> String
decimalOfHex text =
    let
        hexDigits =
            String.toLower text
                |> (\t ->
                        if String.startsWith "0x" t then
                            String.dropLeft 2 t

                        else
                            t
                   )
                |> String.toList

        value c =
            if Char.isDigit c then
                Char.toCode c - Char.toCode '0'

            else
                Char.toCode c - Char.toCode 'a' + 10

        -- digits least significant first; multiply by 16 and add d
        step c digits =
            let
                go ds carry =
                    case ds of
                        [] ->
                            if carry == 0 then
                                []

                            else
                                modBy 10 carry :: go [] (carry // 10)

                        d :: rest ->
                            let
                                n =
                                    d * 16 + carry
                            in
                            modBy 10 n :: go rest (n // 10)
            in
            go digits (value c)
    in
    List.foldl step [] hexDigits
        |> List.reverse
        |> List.map String.fromInt
        |> String.concat
        |> normaliseDecimal


{-| A float literal `d.ddd[e[+-]ddd]` as (mantissa digits, exponent): `0.5` is ("5", -1), `1e300` is
("1", 300), `1.50` is ("150", -2).
-}
floatOf : String -> Maybe { mantissa : String, exponent : Int }
floatOf text =
    let
        lower =
            String.toLower text

        ( number, written ) =
            case String.split "e" lower of
                [ n, ex ] ->
                    ( n, String.toInt (String.replace "+" "" ex) )

                _ ->
                    ( lower, Just 0 )

        ( whole, fraction ) =
            case String.split "." number of
                [ w, f ] ->
                    ( w, f )

                _ ->
                    ( number, "" )
    in
    written
        |> Maybe.andThen
            (\ex ->
                if String.all Char.isDigit (whole ++ fraction) && not (String.isEmpty (whole ++ fraction)) then
                    Just { mantissa = normaliseDecimal (whole ++ fraction), exponent = ex - String.length fraction }

                else
                    Nothing
            )


escapeChar : Char -> Char -> String
escapeChar quote c =
    let
        code =
            Char.toCode c

        hex2 n =
            String.fromList [ hexDigit (n // 16), hexDigit (modBy 16 n) ]
    in
    if c == '\\' then
        "\\\\"

    else if c == quote then
        "\\" ++ String.fromChar c

    else if c == '\n' then
        "\\n"

    else if c == '\t' then
        "\\t"

    else if c == '\u{000D}' then
        "\\r"

    else if code < 0x20 || code == 0x7F then
        "\\x" ++ hex2 code

    else
        String.fromChar c


hexDigit : Int -> Char
hexDigit n =
    if n < 10 then
        Char.fromCode (Char.toCode '0' + n)

    else
        Char.fromCode (Char.toCode 'a' + n - 10)


{-| A Lean string literal, quotes included.
-}
leanString : String -> String
leanString s =
    "\"" ++ String.concat (List.map (escapeChar '"') (String.toList s)) ++ "\""


{-| A Lean char literal, quotes included.
-}
leanChar : Char -> String
leanChar c =
    "'" ++ escapeChar '\'' c ++ "'"
