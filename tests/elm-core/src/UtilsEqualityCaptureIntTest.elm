module UtilsEqualityCaptureIntTest exposing (main)

{-| `(==)` and `(/=)` on `Int` give the same answers when passed as function
values as when applied directly.

On the list `[1, 2, 3, 5, 5]` with target `5`, the operators are passed to the
generic helper `countWith`, giving counts of 2 and 3, and applied in prefix
form inside lambdas passed to the local helper `filter`, keeping the two
matches and the other three elements.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: eq_count: 2
-- CHECK: ne_count: 3
-- CHECK: eq_filter: [5,5]
-- CHECK: ne_filter: [1,2,3]


import Html exposing (text)


{-| Counts the elements `x` of a list for which `pred x target` holds.
-}
countWith : (a -> a -> Bool) -> a -> List a -> Int
countWith pred target xs =
    case xs of
        [] ->
            0

        x :: rest ->
            if pred x target then
                1 + countWith pred target rest

            else
                countWith pred target rest


{-| Keeps the elements of a list for which `keep` holds, in order.
-}
filter : (a -> Bool) -> List a -> List a
filter keep xs =
    case xs of
        [] ->
            []

        x :: rest ->
            if keep x then
                x :: filter keep rest

            else
                filter keep rest


main =
    let
        xs : List Int
        xs =
            [ 1, 2, 3, 5, 5 ]

        _ =
            Debug.log "eq_count" (countWith (==) 5 xs)

        _ =
            Debug.log "ne_count" (countWith (/=) 5 xs)

        _ =
            Debug.log "eq_filter" (filter (\x -> (==) x 5) xs)

        _ =
            Debug.log "ne_filter" (filter (\x -> (/=) x 5) xs)
    in
    text "done"
