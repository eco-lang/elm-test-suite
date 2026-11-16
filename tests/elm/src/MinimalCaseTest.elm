module MinimalCaseTest exposing (main)

{-| A case expression with one rule whose pattern is a variable.

The simplest test of rules d-exp-case, s-exp-case, d-match-first, s-match, d-mrule-match, s-mrule,
d-pat-atpat, s-pat-atpat, d-atpat-var, s-atpat-var of A Standard Definition of Elm?: `case 7 of n ->
n`: the match has one rule, which matches, and its pattern is the atomic pattern `n`, which binds
the value. <https://elm-test-suite.netlify.app/standard/rules/d-exp-case>

-}

-- TAGS: elm-spec, d-exp-case, s-exp-case, d-match-first, s-match, d-mrule-match, s-mrule
-- TAGS: d-pat-atpat, s-pat-atpat, d-atpat-var, s-atpat-var
-- CHECK: testValue: 7

import Html exposing (text)


testValue =
    case 7 of
        n ->
            n


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
