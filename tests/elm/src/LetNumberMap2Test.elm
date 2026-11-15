module LetNumberMap2Test exposing (main)

{-| A list of integer literals combined with a list of `Float`s by `List.map2` is
used at `Float`: `[ 30, 40 ]` scaled by 1.5 and rounded logs `[45,60]`.

The list is let-bound with type `List number`. Inside the `List.map2` lambda
each element is multiplied by `1.5` and added to an element of `[ 0.0, 0.0 ]`,
which makes it a `Float`.

`List.map2` is a library function written in elm/core's kernel code, outside A Standard
Definition of Elm? (Appendix C, Library functions), so this test is not tagged `elm-spec`: it
keeps a `number` literal crossing a two-argument kernel function. `LetNumberLocalMap2Test` checks
the same typing with a `map2` written in the program.

-}

-- CHECK: map2: [45,60]

import Html exposing (text)


main =
    let
        xs =
            [ 30, 40 ]

        result =
            List.map2 (\x y -> round (x * 1.5 + y)) xs [ 0.0, 0.0 ]

        _ =
            Debug.log "map2" result
    in
    text "done"
