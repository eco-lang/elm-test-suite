module UrlIssue54PercentEncodeLoneSurrogateTest exposing (main)

{-| `Url.percentEncode` throws on a lone surrogate.

<https://github.com/elm/url/issues/54>

Elm 0.19.1 (elm/url 1.0.0) calls `encodeURIComponent` unguarded, which throws `URIError: URI
malformed` for "\u{d800}" (a valid Elm String). `percentEncode : String -> String` must return a
string (`percentDecode` already catches the same exception).

This test is probably wrong under A Standard Definition of Elm? It writes the lone surrogate as
the escape `"\u{d800}"`, which ruling A8 makes invalid: an escape must denote a Unicode scalar
value. <https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode> Under A8 the program does not compile, so a
compiler that follows the book fails this test without reaching the bug. `elm-url`'s
`UrlPercentEncodeLoneSurrogateTest` tests the same bug with the lone surrogate computed by
`Char.fromCode`. The test is kept as it is because it is the issue's program.

-}

-- TAGS: elm19-bug
-- CHECK: encoded:

import Html exposing (text)
import Url


main =
    let
        _ =
            Debug.log "encoded" (String.length (Url.percentEncode "a\u{d800}b") > 0)
    in
    text "done"
