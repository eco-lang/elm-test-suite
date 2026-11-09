module InfixPrecOrOverPipeTest exposing (main)

{-| `||` (precedence 2) binds more tightly than `|>` (precedence 0).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`True || False |> not` is `(True || False) |> not`, `False`, not
`True || (False |> not)`, `True`.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, df:or, b:Basics.apR, b:Basics.not
-- CHECK: or then pipe: False

import Html


main =
    let
        _ =
            Debug.log "or then pipe" (True || False |> not)
    in
    Html.text "done"
