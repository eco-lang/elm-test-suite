module InfixAssocPipesTest exposing (main)

{-| `|>` associates to the left and `<|` to the right.

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): operators of equal precedence that both associate to the left group to the
left, and both to the right, to the right. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

The book's examples: `a |> f |> g` is `(a |> f) |> g`, and `f <| g <| a` is `f <| (g <| a)`.
`3 |> negate |> abs` is 3, and `negate <| abs <| -3` is -3; grouped the other way, neither
would type.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.apR, b:Basics.apL
-- CHECK: pipe right twice: 3
-- CHECK: pipe left twice: -3

import Html


main =
    let
        _ =
            Debug.log "pipe right twice" (3 |> negate |> abs)

        _ =
            Debug.log "pipe left twice" (negate <| abs <| -3)
    in
    Html.text "done"
