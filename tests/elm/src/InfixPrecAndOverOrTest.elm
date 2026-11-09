module InfixPrecAndOverOrTest exposing (main)

{-| `&&` (precedence 3) binds more tightly than `||` (precedence 2).

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): an operator of higher precedence binds more tightly than one of lower
precedence, and application more tightly than any operator. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

`True || False && False` is `True || (False && False)`, `True`, not
`(True || False) && False`, `False`.

-}

-- TAGS: elm-spec, fig:core-fixities, df:and, df:or
-- CHECK: or then and: True

import Html


main =
    let
        _ =
            Debug.log "or then and" (True || False && False)
    in
    Html.text "done"
