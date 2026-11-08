module CharLiteralSurrogateEscapeTest exposing (main)

{-| `'\u{D800}'` is not a Char literal: a surrogate code point is not a character.

The Definition of Standard Elm, ruling A8: the escape `\u{h}` denotes a Unicode scalar value, so
the surrogate code points D800 to DFFF are not allowed, in Char literals as in String literals.
<https://elm-test-suite.netlify.app/standard/syntax-core#fig-core-escapes>

This is how <https://github.com/elm/compiler/issues/2366> is resolved under A8. The issue's program
(`elm-bugs`'s `CompilerIssue2366LoneSurrogateCharLiteralTest`) uses `'\u{D800}'` and
`'\u{DFFF}'`; Elm 0.19.2, Elm 0.19.3 and Lamdera 1.5.0 write such literals into the generated
JavaScript as raw surrogates, which are not valid UTF-8, so the literals become replacement
characters. Under A8 the program is rejected instead, and no surrogate literal reaches the code
generator; a program that needs the value computes it, `Char.fromCode 0xD800`. Elm 0.19.1 accepts
the literal, and so do the others. `elm-bugs`'s `StandardA8SurrogateEscapeTest` checks the same
for a String literal.

-}

-- COMPILE-ERROR: a surrogate escape in a Char literal
-- CHECK: {{-- [A-Z ]+ -}}

import Html


isHighSurrogate : Char -> Bool
isHighSurrogate c =
    '\u{D800}' <= c && c <= '\u{DBFF}'


main =
    Html.text (if isHighSurrogate 'a' then "yes" else "no")
