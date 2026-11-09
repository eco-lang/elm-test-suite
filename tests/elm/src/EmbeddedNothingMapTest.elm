module EmbeddedNothingMapTest exposing (main)

{-| A local `map` with a function that matches `Maybe` maps each `Nothing` to -1 and
each `Just` to its payload.
-}

-- TAGS: elm-spec, d-pat-con, d-atpat-con
-- CHECK: results: [-1,1,-1,2]

import Html exposing (text)


extract m =
    case m of
        Just x ->
            x

        Nothing ->
            -1


map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


main =
    let
        items =
            [ Nothing, Just 1, Nothing, Just 2 ]

        results =
            map extract items

        _ = Debug.log "results" results
    in
    text "done"
