module LetNumberLocalMap2Test exposing (main)

{-| A list of integer literals combined with a list of `Float`s by a two-argument mapping function
is used at `Float`: `[ 30, 40 ]` scaled by 1.5 and rounded logs `[45,60]`.

The list is let-bound with type `List number`. Inside the lambda that `map2` applies, each
element is multiplied by `1.5` and added to an element of `[ 0.0, 0.0 ]`, which makes it a
`Float`. `map2` is written in the program, so the test keeps to A Standard Definition of Elm?'s
basis; `LetNumberMap2Test` checks the same typing through elm/core's `List.map2`.

-}

-- TAGS: elm-spec, s-dec-group, s-atexp-scon, d-atexp-scon
-- CHECK: map2: [45,60]

import Html exposing (text)


{-| Combines the elements of two lists pairwise, stopping at the end of the shorter.
-}
map2 : (a -> b -> c) -> List a -> List b -> List c
map2 f xs ys =
    case ( xs, ys ) of
        ( x :: xrest, y :: yrest ) ->
            f x y :: map2 f xrest yrest

        _ ->
            []


main =
    let
        xs =
            [ 30, 40 ]

        result =
            map2 (\x y -> round (x * 1.5 + y)) xs [ 0.0, 0.0 ]

        _ =
            Debug.log "map2" result
    in
    text "done"
