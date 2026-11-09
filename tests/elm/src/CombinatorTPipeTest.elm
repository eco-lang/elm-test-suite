module CombinatorTPipeTest exposing (main)

{-| The T combinator, built from S and K, passing `[ 1, 2, 3 ]` to the composition of `sum` and `map ((*) 2)`: the result is 12.

`t` is `c i`, where `c = s (b b s) (k k)`, `b = s (k s) k` and `i = s k k`.
`sum` and `map` are defined in the module by pattern matching on lists.

-}

-- TAGS: elm-spec, sm-topdec-value, d-app-closure, d-app-basic-partial, d-atexp-op, d-app-basic-apply
-- CHECK: result: 12

import Html exposing (text)


k a _ = a

s bf uf x = bf x (uf x)

b = s (k s) k

c = s (b b s) (k k)

i = s k k

t = c i


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
        _ = Debug.log "result" (t [ 1, 2, 3 ] (b sum (map ((*) 2))))
    in
    text "done"
