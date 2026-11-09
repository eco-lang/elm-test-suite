module CharLiteralPatternMatchMinimalTest exposing (main)

{-| A Char literal pattern for the double quote `'"'` matches at increasing depths of nesting:
bare, inside a tuple, inside a `Maybe`, and inside a `Maybe ( Char, String )`.

Every case should log `"y"`. The same pattern matched against a Char taken from a String by the
library function `String.uncons` is checked by elm-core's CharUnconsPatternTest.

-}

-- TAGS: elm-spec, d-atpat-scon, d-atpat-tuple, d-pat-con
-- CHECK: m1_bareChar: "y"
-- CHECK: m2_charInTuple: "y"
-- CHECK: m3_charInMaybe: "y"
-- CHECK: m4_charInMaybeTuple: "y"

import Html exposing (text)


main =
    let
        -- m1: bare Char
        m1 =
            case '"' of
                '"' ->
                    "y"

                _ ->
                    "n"

        -- m2: Char inside a tuple
        m2 =
            case ( '"', 0 ) of
                ( '"', _ ) ->
                    "y"

                _ ->
                    "n"

        -- m3: Char inside a Maybe
        m3 =
            case Just '"' of
                Just '"' ->
                    "y"

                _ ->
                    "n"

        -- m4: Char inside a Maybe (Char, X), the shape String.uncons gives
        m4 =
            case Just ( '"', "x" ) of
                Just ( '"', _ ) ->
                    "y"

                _ ->
                    "n"

        _ =
            Debug.log "m1_bareChar" m1

        _ =
            Debug.log "m2_charInTuple" m2

        _ =
            Debug.log "m3_charInMaybe" m3

        _ =
            Debug.log "m4_charInMaybeTuple" m4
    in
    text "done"
