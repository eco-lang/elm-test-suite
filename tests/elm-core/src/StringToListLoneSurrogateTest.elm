module StringToListLoneSurrogateTest exposing (main)

{-| `String.toList` of a string holding a lone low surrogate returns one `Char`.

The bug of <https://github.com/elm/core/issues/1060>, with a program that follows A Standard Definition of Elm? The issue, and `CoreIssue1060StringToListLoneSurrogateTest` (tagged `elm19-bug`), write the
lone surrogate as the escape `"\u{dd56}"`, which ruling A8 makes invalid: an escape must denote a
Unicode scalar value. <https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode>

Here the lone surrogate is computed, `String.fromChar (Char.fromCode 0xDD56)`, so the program is
valid under A8, and the string is the same. Elm 0.19.1 still loops forever on `String.toList` of it
until it runs out of memory; the test caps the JavaScript heap so that this fails quickly.

-}

-- CHECK: length: 1
-- ENV: NODE_OPTIONS=--max-old-space-size=256

import Html exposing (text)


main =
    let
        loneLowSurrogate =
            String.fromChar (Char.fromCode 0xDD56)

        _ =
            Debug.log "length" (List.length (String.toList loneLowSurrogate))
    in
    text "done"
