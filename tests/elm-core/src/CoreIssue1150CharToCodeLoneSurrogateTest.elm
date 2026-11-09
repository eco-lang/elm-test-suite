module CoreIssue1150CharToCodeLoneSurrogateTest exposing (main)

{-| `Char.toCode` returns NaN, typed as `Int`, for a lone surrogate.

<https://github.com/elm/core/issues/1150>

Elm 0.19.1 gives `Char.toCode (Char.fromCode 0xD800)` = `NaN`. A value of type `Int` must be an
integer.

A Standard Definition of Elm?, the basis entries Char.fromCode and Char.toCode: for an integer that
is not a Unicode scalar value, such as the surrogate 0xD800, `Char.fromCode` gives a character of
the implementation's choosing; it is a character all the same, and the code of every character is
an Int, in the Int range. So whatever `Char.fromCode 0xD800` is, `Char.toCode` of it is an
integer; NaN is the divergence the book records under ruling A52.
<https://elm-test-suite.netlify.app/standard/basis/Char/fromCode>

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Char.fromCode, b:Char.toCode, b:Char.Char, b:Basics.Int
-- CHECK: {{code: [0-9]+(\n|$)}}

import Html exposing (text)


main =
    let
        _ =
            Debug.log "code" (Char.toCode (Char.fromCode 0xD800))
    in
    text "done"
