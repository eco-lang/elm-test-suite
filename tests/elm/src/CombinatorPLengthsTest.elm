module CombinatorPLengthsTest exposing (main)

{-| The P combinator, which applies one function to two arguments and combines the results: `p (+) length [ 1, 2, 3 ] [ 4, 5 ]` is 5.

`length` is defined in the module by pattern matching on lists.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-closure, d-app-basic-partial, d-app-basic-apply
-- CHECK: result: 5

import Html exposing (text)


p bf uf x y = bf (uf x) (uf y)


length list =
    case list of
        [] -> 0
        _ :: rest -> 1 + length rest


main =
    let
        _ = Debug.log "result" (p (+) length [ 1, 2, 3 ] [ 4, 5 ])
    in
    text "done"
