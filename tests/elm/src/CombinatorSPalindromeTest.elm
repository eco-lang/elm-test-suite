module CombinatorSPalindromeTest exposing (main)

{-| The S combinator with a one-argument string function: `s (++) bang "straw"` is `"straw" ++ bang "straw"`, which is `"strawstraw!"`.

`bang` appends `"!"` to its argument.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-closure, d-app-basic-partial, d-app-basic-apply
-- CHECK: result: "strawstraw!"

import Html exposing (text)


s bf uf x = bf x (uf x)


bang str = str ++ "!"


main =
    let
        _ = Debug.log "result" (s (++) bang "straw")
    in
    text "done"
