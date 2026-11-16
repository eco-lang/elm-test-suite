module MinimalCaseNextRuleTest exposing (main)

{-| A value the first rule of a case does not match goes to the next rule.

The simplest test of rules d-match-next, d-mrule-fail, d-atpat-scon-fail, d-atpat-wild, s-atpat-wild
of A Standard Definition of Elm?: in `case 2 of 1 -> 10 ; _ -> 20` the constant pattern `1` fails on
`2`, so the rule fails and the wildcard rule gives `20`.
<https://elm-test-suite.netlify.app/standard/rules/d-match-next>

-}

-- TAGS: elm-spec, d-match-next, d-mrule-fail, d-atpat-scon-fail, d-atpat-wild, s-atpat-wild
-- CHECK: testValue: 20

import Html exposing (text)


testValue =
    case 2 of
        1 ->
            10

        _ ->
            20


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
