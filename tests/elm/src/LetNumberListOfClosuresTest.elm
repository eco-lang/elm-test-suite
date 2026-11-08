module LetNumberListOfClosuresTest exposing (main)

{-| A let-bound `number` captured by two anonymous functions stored in a list,
each applied to a `Float`, is a `Float`.

With `n = 30`, `fns = [ \x -> x * n, \x -> x + n ]`, and applying each to 1.0
gives `[30,31]`.

-}

-- TAGS: elm-spec, s-dec-group, s-atexp-scon, d-atexp-scon
-- CHECK: listclos: [30,31]

import Html exposing (text)


main =
    let
        n =
            30

        fns =
            [ \x -> x * n, \x -> x + n ]

        result =
            List.map (\f -> round (f 1.0)) fns

        _ =
            Debug.log "listclos" result
    in
    text "done"
