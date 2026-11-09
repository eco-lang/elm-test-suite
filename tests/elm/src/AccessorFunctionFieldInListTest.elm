module AccessorFunctionFieldInListTest exposing (main)

{-| Record accessors for function-typed fields can be used as list elements.

`.op` and `.op2` read fields of type `Int -> Int`. They are placed in a list of
type `List (Ops -> Int -> Int)`. A `case` on the list takes the two elements out,
and each is applied to one record and then to 10, giving `10 + 1` and `10 * 2`.

-}

-- TAGS: elm-spec, s-atpat-record, d-patrow-field
-- CHECK: results: [11,20]

import Html exposing (text)


type alias Ops =
    { op : Int -> Int, op2 : Int -> Int }


main =
    let
        ops : Ops
        ops =
            { op = \n -> n + 1, op2 = \n -> n * 2 }

        getters : List (Ops -> Int -> Int)
        getters =
            [ .op, .op2 ]

        results : List Int
        results =
            case getters of
                [ g1, g2 ] ->
                    [ g1 ops 10, g2 ops 10 ]

                _ ->
                    []

        _ =
            Debug.log "results" results
    in
    text "done"
