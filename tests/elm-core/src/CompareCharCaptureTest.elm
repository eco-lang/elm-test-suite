module CompareCharCaptureTest exposing (main)

{-| A local insertion sort, `sortWith`, on a list of `Char`, given `compare` itself and given a lambda that calls `compare` with its arguments swapped.

  - `sorted`: `sortWith compare` sorts `[ 'c', 'a', 'd', 'e', 'b' ]` into ascending order.
  - `reverse_sorted`: `sortWith (\a b -> compare b a)` sorts the same list into descending order.

-}

-- TAGS: elm-spec, d-app-basic-partial, d-app-basic-apply
-- CHECK: sorted: ['a','b','c','d','e']
-- CHECK: reverse_sorted: ['e','d','c','b','a']


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
        xs : List Char
        xs =
            [ 'c', 'a', 'd', 'e', 'b' ]

        _ =
            Debug.log "sorted" (sortWith compare xs)

        _ =
            Debug.log "reverse_sorted" (sortWith (\a b -> compare b a) xs)
    in
    text "done"
