module CompilerIssue2366LoneSurrogateCharLiteralTest exposing (main)

{-| Char literals for surrogate code points compare correctly against a string's lone surrogates.

<https://github.com/elm/compiler/issues/2366>

`String.left 3 "ab😀"` cuts the emoji in half, leaving `"ab"` followed by a lone high surrogate.
Filtering out every `Char` between the literals `'\u{D800}'` and `'\u{DFFF}'` must remove it,
giving `"ab"` of length 2, as Elm 0.19.1 does. Elm 0.19.2, Elm 0.19.3 and Lamdera 1.5.0 write
those literals into the generated JavaScript as raw lone surrogates instead of escapes, so the
output is not valid UTF-8, the literals no longer hold surrogates, and the program logs
`"ab�undefined"` of length 12.

This test is probably wrong under A Standard Definition of Elm? Its literals `'\u{D800}'` and
`'\u{DFFF}'` are surrogate escapes, which ruling A8 makes invalid: an escape must denote a Unicode
scalar value, and a surrogate is half of a UTF-16 encoding, not a character. <https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode>
Under A8 the program does not compile, so a compiler that follows the book fails this test; the
issue is resolved by rejecting the literal, and `elm`'s `CharLiteralSurrogateEscapeTest` tests
that. The test is kept as it is because it is the issue's program.

A Standard Definition of Elm? does not accept this as a bug: the program is not valid Elm. The
escape `\u{h}` denotes a Unicode scalar value, so `'\u{D800}'` and `'\u{DFFF}'` are not
character constants (restriction core-escape-unicode, ruling A8), and the program is rejected.
CharLiteralSurrogateEscapeTest checks that. Elm 0.19.1 accepts it, so this test passes there
(an XPASS).
<https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: the book rejects the program: surrogate escapes are not escape sequences (A8)
-- CHECK: cleaned: "ab"
-- CHECK: length: 2
-- CHECK: cut: 3

import Html exposing (text)


{-| Removes every UTF-16 surrogate code unit from a string.
-}
clean : String -> String
clean =
    String.filter (not << isSurrogate)


{-| Whether a `Char` is in the surrogate range, written with surrogate `Char` literals.
-}
isSurrogate : Char -> Bool
isSurrogate char =
    '\u{D800}' <= char && char <= '\u{DFFF}'


main =
    let
        cut =
            String.left 3 "ab😀"

        result =
            clean cut

        _ =
            Debug.log "cut" (String.length cut)

        _ =
            Debug.log "cleaned" result

        _ =
            Debug.log "length" (String.length result)
    in
    text "done"
