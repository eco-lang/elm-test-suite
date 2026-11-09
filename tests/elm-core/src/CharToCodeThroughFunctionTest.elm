module CharToCodeThroughFunctionTest exposing (main)

{-| `Char.toCode` of a character returned from a top-level function, here an
identity function applied to `'A'`, gives 65.

A Standard Definition of Elm?, the basis entry Char.toCode: the code of the character with code
point h is h. <https://elm-test-suite.netlify.app/standard/basis/Char/toCode>

-}

-- TAGS: elm-spec, b:Char.toCode, d-app-closure
-- CHECK: code: 65


import Char
import Html exposing (text)


identityChar : Char -> Char
identityChar c =
    c


main =
    let
        c =
            identityChar 'A'

        _ =
            Debug.log "code" (Char.toCode c)
    in
    text "done"
