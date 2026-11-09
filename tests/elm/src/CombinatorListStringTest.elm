module CombinatorListStringTest exposing (main)

{-| SKI-style combinators applied to lists, strings and functions over them, each printing its result.

The combinators are `k`, `s`, and the point-free `i = s k k`, `b = s (k s) k`,
`c = s (b b s) (k k)` and `t = c i`, together with directly written `sp`
(`bf (uf1 x) (uf2 x)`), `w` (`bf x x`) and `p` (`bf (uf x) (uf y)`). The list and
string functions `sum`, `map`, `length` and `bang` are defined in the module. The tests:

  - `b_sum_map`: `b` composes `sum` with `map ((+) 1)` over `[ 1, 2, 3 ]`, giving 9.
  - `sp_mul`: `sp (*) ((+) 1) ((*) 2) 6` is `7 * 12`, giving 84.
  - `w_concat`: `w (++) "hi"` is `"hihi"`.
  - `c_cons`: `c (::) [ 2, 3 ] 1` is `[ 1, 2, 3 ]`.
  - `s_palindrome`: `s (++) bang "straw"` is `"straw" ++ "straw!"`, giving `"strawstraw!"`.
  - `t_pipe`: `t` passes `[ 1, 2, 3 ]` to the composition of `sum` and `map ((*) 2)`, giving 12.
  - `p_lengths`: `p (+) length` adds the lengths of a three- and a two-element list, giving 5.

-}

-- TAGS: elm-spec, sm-topdec-value, d-atexp-op, d-app-basic-partial, d-app-closure, d-app-basic-apply
-- CHECK: b_sum_map: 9
-- CHECK: sp_mul: 84
-- CHECK: w_concat: "hihi"
-- CHECK: c_cons: [1,2,3]
-- CHECK: s_palindrome: "strawstraw!"
-- CHECK: t_pipe: 12
-- CHECK: p_lengths: 5

import Html exposing (text)


k a _ = a

s bf uf x = bf x (uf x)

i = s k k

b = s (k s) k

c = s (b b s) (k k)

sp bf uf1 uf2 x = bf (uf1 x) (uf2 x)

t = c i

w bf x = bf x x

p bf uf x y = bf (uf x) (uf y)


sum list =
    case list of
        [] -> 0
        x :: rest -> x + sum rest


map f list =
    case list of
        [] -> []
        x :: rest -> f x :: map f rest


length list =
    case list of
        [] -> 0
        _ :: rest -> 1 + length rest


bang str = str ++ "!"


main =
    let
        _ = Debug.log "b_sum_map" (b sum (map ((+) 1)) [ 1, 2, 3 ])
        _ = Debug.log "sp_mul" (sp (*) ((+) 1) ((*) 2) 6)
        _ = Debug.log "w_concat" (w (++) "hi")
        _ = Debug.log "c_cons" (c (::) [ 2, 3 ] 1)
        _ = Debug.log "s_palindrome" (s (++) bang "straw")
        _ = Debug.log "t_pipe" (t [ 1, 2, 3 ] (b sum (map ((*) 2))))
        _ = Debug.log "p_lengths" (p (+) length [ 1, 2, 3 ] [ 4, 5 ])
    in
    text "done"
