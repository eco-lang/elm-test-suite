module UtilsEqualityCaptureCharTest exposing (main)

{-| `(==)` and `(/=)` on `Char` give the same answers when passed as function
values as when applied directly.

On the list `['a','b','c','x','x']` with target `'x'`, the operators are passed
to the generic helper `countWith`, giving counts of 2 and 3, and applied in prefix
form inside lambdas passed to the local helper `filter`, keeping the two
matches and the other three elements.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: eq_count: 2
-- CHECK: ne_count: 3
-- CHECK: eq_filter: ['x','x']
-- CHECK: ne_filter: ['a','b','c']


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
        xs : List Char
        xs =
            [ 'a', 'b', 'c', 'x', 'x' ]

        _ =
            Debug.log "eq_count" (countWith (==) 'x' xs)

        _ =
            Debug.log "ne_count" (countWith (/=) 'x' xs)

        _ =
            Debug.log "eq_filter" (filter (\x -> (==) x 'x') xs)

        _ =
            Debug.log "ne_filter" (filter (\x -> (/=) x 'x') xs)
    in
    text "done"
