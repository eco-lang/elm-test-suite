module StringCreationMatrixTest exposing (main)

{-| The same string produced in different ways is `==`, and matches the same string pattern in a
`case`.

The string `"abc123"` is produced four ways: as a literal, as `"abc" ++ "123"`, as
`"ab" ++ "c1" ++ "23"`, and as `"" ++ "abc123" ++ ""`. The test logs two results:

  - `eq`: all four are equal;
  - `case`: the three concatenated ones each match the `"abc123"` pattern.

The same string made by library functions, and its use as a `Dict` key, are checked by
StringCreationLibraryMatrixTest.

-}

-- TAGS: elm-spec, d-atpat-scon
-- CHECK: Creation.eq: True
-- CHECK: Creation.case: True

import Html exposing (text)


classify : String -> String
classify s =
    case s of
        "abc123" ->
            "matched"

        _ ->
            "no"


main : Html.Html msg
main =
    let
        viaLiteral =
            "abc123"

        viaConcat =
            "abc" ++ "123"

        viaThree =
            "ab" ++ "c1" ++ "23"

        viaEmpty =
            "" ++ "abc123" ++ ""

        eq =
            (viaLiteral == viaConcat)
                && (viaConcat == viaThree)
                && (viaThree == viaEmpty)

        caseOk =
            (classify viaConcat == "matched")
                && (classify viaThree == "matched")
                && (classify viaEmpty == "matched")

        _ =
            Debug.log "Creation.eq" eq

        _ =
            Debug.log "Creation.case" caseOk
    in
    text ""
