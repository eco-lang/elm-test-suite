module CaseBranchSelectionTest exposing (main)

{-| A `case` tries its branches in order: a branch whose pattern fails passes the value on, and
the first that matches is evaluated with its pattern's bindings.

A Standard Definition of Elm?, rules d-match-fail and d-mrule-match: a match rule whose pattern
fails passes to the next, and one whose pattern matches evaluates its body with the variables
the pattern binds. Rules s-mrule, s-atpat-var and s-atpat-wild type the branches: a variable
pattern binds the value at the scrutinee's type, a wildcard binds nothing. <https://elm-test-suite.netlify.app/standard/rules/d-match-fail>

-}

-- TAGS: elm-spec, d-match-fail, d-mrule-match, s-mrule, s-atpat-var, s-atpat-wild
-- CHECK: classify: ["zero","one","pair 2 3","other 9"]
-- CHECK: first match wins: "specific"

import Html


type Shape
    = Zero
    | One
    | Pair Int Int
    | Other Int


classify : Shape -> String
classify s =
    case s of
        Zero ->
            "zero"

        One ->
            "one"

        Pair a b ->
            "pair " ++ Debug.toString a ++ " " ++ Debug.toString b

        other ->
            case other of
                Other n ->
                    "other " ++ Debug.toString n

                _ ->
                    "unreachable"


overlap : Int -> String
overlap n =
    case n of
        1 ->
            "specific"

        _ ->
            "general"


main =
    let
        _ =
            Debug.log "classify" [ classify Zero, classify One, classify (Pair 2 3), classify (Other 9) ]

        _ =
            Debug.log "first match wins" (overlap 1)
    in
    Html.text "done"
