module StandardA8SurrogateEscapeTest exposing (..)

{-| `\u{D800}` is not an escape sequence: a surrogate code point is not a character.

A Standard Definition of Elm?, ruling A8: the escape `\u{h}` denotes a Unicode scalar value, so
the surrogate code points D800 to DFFF are not allowed. <https://elm-test-suite.netlify.app/standard/syntax-core#fig-core-escapes>

Elm 0.19.1 accepts `"\u{D800}"` and makes a string holding a lone surrogate. `elm`'s
`CharLiteralSurrogateEscapeTest` checks the same for a Char literal. Three tests tagged
`elm19-bug` use surrogate escapes because their issues do (`CompilerIssue2366LoneSurrogateCharLiteralTest`,
`CoreIssue1060StringToListLoneSurrogateTest`, `UrlIssue54PercentEncodeLoneSurrogateTest`); each
says so, and names a test that follows A8.

-}

-- TAGS: elm19-bug
-- COMPILE-ERROR: a surrogate escape
-- CHECK: {{-- [A-Z ]+ -}}

import Html


loneSurrogate : String
loneSurrogate =
    "\u{D800}"


main =
    Html.text (String.fromInt (String.length loneSurrogate))
