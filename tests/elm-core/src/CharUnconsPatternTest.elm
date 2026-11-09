module CharUnconsPatternTest exposing (main)

{-| A Char taken from a String by `String.uncons` matches the Char literal pattern `'"'`, and is
`==` to the literal.

`String.uncons "\"x"` gives `Just ( '"', "x" )`. The first case matches it with the literal
pattern, the second binds the Char and compares it with `==`. Both should log `"y"`. The same
patterns on Chars written as literals are checked by elm's CharLiteralPatternMatchMinimalTest.

-}

-- CHECK: uncons_pat: "y"
-- CHECK: uncons_eq: "y"

import Html exposing (text)


main =
    let
        withPattern =
            case String.uncons "\"x" of
                Just ( '"', _ ) ->
                    "y"

                _ ->
                    "n"

        withEq =
            case String.uncons "\"x" of
                Just ( c, _ ) ->
                    if c == '"' then
                        "y"

                    else
                        "n"

                Nothing ->
                    "n"

        _ =
            Debug.log "uncons_pat" withPattern

        _ =
            Debug.log "uncons_eq" withEq
    in
    text "done"
