module ParenthesesTest exposing (main)

{-| Parentheses around an expression, a pattern or a type change nothing but the grouping.

A Standard Definition of Elm?, rules s-atexp-paren and d-atexp-paren: `(e)` has the type and the
value of `e`; rules s-atpat-paren and d-atpat-paren: `(p)` matches as `p`, and fails as `p`
does; rule s-ty-paren: `(t)` is the type `t`. An atomic expression or pattern stands for a full
one (rules s-exp-atexp, d-exp-atexp, s-pat-atpat, d-pat-atpat). <https://elm-test-suite.netlify.app/standard/rules/d-atexp-paren>

-}

-- TAGS: elm-spec, s-atexp-paren, d-atexp-paren, s-atpat-paren, d-atpat-paren, s-ty-paren
-- TAGS: s-exp-atexp, d-exp-atexp, s-pat-atpat, d-pat-atpat
-- CHECK: grouped: 9
-- CHECK: ungrouped: 7
-- CHECK: redundant: 5
-- CHECK: nested pattern: [3,0,-1]
-- CHECK: parenthesised types: [2,4]

import Html


inner : Maybe (Maybe Int) -> Int
inner m =
    case m of
        Just (Just n) ->
            n

        Just (Nothing) ->
            0

        (Nothing) ->
            -1


doubleAll : (List (Int)) -> (List Int)
doubleAll xs =
    case xs of
        [] ->
            []

        x :: rest ->
            (*) 2 x :: doubleAll rest


main =
    let
        _ =
            Debug.log "grouped" ((1 + 2) * 3)

        _ =
            Debug.log "ungrouped" (1 + 2 * 3)

        _ =
            Debug.log "redundant" ((((5))))

        _ =
            Debug.log "nested pattern" [ inner (Just (Just 3)), inner (Just Nothing), inner Nothing ]

        _ =
            Debug.log "parenthesised types" (doubleAll [ 1, 2 ])
    in
    Html.text "done"
