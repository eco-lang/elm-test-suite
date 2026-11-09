module CombinatorPLengthsTest exposing (main)

{-| The P combinator, which applies one function to two arguments and combines the results: `p (+) List.length [ 1, 2, 3 ] [ 4, 5 ]` is 5.
-}

-- TAGS: elm-spec, d-atexp-op, d-app-closure, d-app-basic-partial, d-app-basic-apply
-- CHECK: result: 5

import Html exposing (text)


p bf uf x y = bf (uf x) (uf y)


main =
    let
        _ = Debug.log "result" (p (+) List.length [ 1, 2, 3 ] [ 4, 5 ])
    in
    text "done"
