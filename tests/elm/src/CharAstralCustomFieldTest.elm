module CharAstralCustomFieldTest exposing (main)

{-| An astral `Char` (code point above 0xFFFF) stored in a custom-type
constructor's field keeps its code point when read back by pattern matching.

`Box` has a single constructor and is unwrapped by an argument pattern. `Shape`
has three constructors, two of which carry a `Char`, and is read with a case
expression; its `Empty` constructor gives -1. How `Debug.log` prints such a value is checked by
`CharAstralCustomFieldShowTest`.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h, and `\u{h}` denotes that character (Figure 1, Escape Sequences), as does the
character itself written in a constant. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode> A constructor's field holds the
value it was given (rules d-app-con and d-pat-con).

-}

-- TAGS: elm-spec, b:Char.toCode, d-atexp-scon, d-app-con, d-pat-con, d-exp-case
-- CHECK: box_code: 128512
-- CHECK: shape_codes: [128512,119070,-1]

import Html exposing (text)


type Box
    = Box Int Char


type Shape
    = Dot Char
    | Pair Int Char
    | Empty


boxCode : Box -> Int
boxCode (Box _ c) =
    Char.toCode c


shapeCode : Shape -> Int
shapeCode s =
    case s of
        Dot c ->
            Char.toCode c

        Pair _ c ->
            Char.toCode c

        Empty ->
            -1


main =
    let
        _ =
            Debug.log "box_code" (boxCode (Box 3 '😀'))

        _ =
            Debug.log "shape_codes" [ shapeCode (Dot '😀'), shapeCode (Pair 1 '\u{1D11E}'), shapeCode Empty ]
    in
    text "done"
