module CombinatorBSumMapTest exposing (main)

{-| The B combinator, built from S and K, composing `sum` with a partially applied `map`: the sum of `[ 1, 2, 3 ]` each plus one is 9.

`b` is the point-free definition `s (k s) k`, applied to `sum` and to `map`
partially applied to `(+) 1`, both defined in the module by pattern matching
on lists.

-}

-- TAGS: elm-spec, sm-topdec-value, d-app-closure, d-app-basic-partial, d-atexp-op, d-app-basic-apply
-- CHECK: result: 9

import Html exposing (text)


k a _ = a

s bf uf x = bf x (uf x)

b = s (k s) k


sum list =
    case list of
        [] -> 0
        x :: rest -> x + sum rest


map f list =
    case list of
        [] -> []
        x :: rest -> f x :: map f rest


main =
    let
        _ = Debug.log "result" (b sum (map ((+) 1)) [ 1, 2, 3 ])
    in
    text "done"
