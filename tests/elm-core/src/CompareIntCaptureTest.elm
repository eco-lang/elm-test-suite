module CompareIntCaptureTest exposing (main)

{-| `compare` on `Int` passed as a function value to a local insertion sort,
`sortWith`.

The list is sorted once with `compare` itself and once with a lambda that
swaps its arguments, which sorts it in descending order.

-}

-- TAGS: elm-spec, d-app-basic-partial, d-app-basic-apply
-- CHECK: sorted: [1,2,3,4,5]
-- CHECK: reverse_sorted: [5,4,3,2,1]


import Html exposing (text)


{-| Sorts a list by insertion, ordering its elements with `cmp`.
-}
sortWith : (a -> a -> Order) -> List a -> List a
sortWith cmp xs =
    case xs of
        [] ->
            []

        x :: rest ->
            insertWith cmp x (sortWith cmp rest)


insertWith : (a -> a -> Order) -> a -> List a -> List a
insertWith cmp x ys =
    case ys of
        [] ->
            [ x ]

        y :: rest ->
            case cmp x y of
                GT ->
                    y :: insertWith cmp x rest

                _ ->
                    x :: ys


main =
    let
        xs : List Int
        xs =
            [ 3, 1, 4, 5, 2 ]

        _ =
            Debug.log "sorted" (sortWith compare xs)

        _ =
            Debug.log "reverse_sorted" (sortWith (\a b -> compare b a) xs)
    in
    text "done"
