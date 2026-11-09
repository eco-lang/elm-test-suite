module UrlPercentEncodeLoneSurrogateTest exposing (main)

{-| `Url.percentEncode` returns a string for a string holding a lone surrogate.

The bug of <https://github.com/elm/url/issues/54>, with a program that follows A Standard Definition of Elm? The issue, and `UrlIssue54PercentEncodeLoneSurrogateTest` (tagged `elm19-bug`), write the
lone surrogate as the escape `"\u{d800}"`, which ruling A8 makes invalid: an escape must denote a
Unicode scalar value. <https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode>

Here the lone surrogate is computed, `Char.fromCode 0xD800`, so the program is valid under A8, and
the string is the same. elm/url 1.0.0 calls `encodeURIComponent` unguarded, which throws `URIError:
URI malformed` for it. `percentEncode : String -> String` must return a string (`percentDecode`
already catches the same exception).

-}

-- CHECK: encoded: True

import Html exposing (text)
import Url


main =
    let
        withLoneSurrogate =
            "a" ++ String.fromChar (Char.fromCode 0xD800) ++ "b"

        _ =
            Debug.log "encoded" (String.length (Url.percentEncode withLoneSurrogate) > 0)
    in
    text "done"
