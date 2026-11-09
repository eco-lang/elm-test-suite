module UtilsOrderingCaptureFloatTest exposing (main)

{-| `(<)`, `(<=)`, `(>)` and `(>=)` on `Float` give the right answers when
passed as function values or applied in prefix form.

On the list `[1, 2, 3, 4, 5]` (as floats) with pivot `3.0`, each operator is
applied in prefix form inside a lambda passed to the local helper `filter`, and
`(<)` and `(>=)` are also passed to the generic helper `countWith`, counting 2
and 3 elements.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: lt_filter: [1,2]
-- CHECK: le_filter: [1,2,3]
-- CHECK: gt_filter: [4,5]
-- CHECK: ge_filter: [3,4,5]
-- CHECK: count_lt: 2
-- CHECK: count_ge: 3


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
        xs : List Float
        xs =
            [ 1.0, 2.0, 3.0, 4.0, 5.0 ]

        _ =
            Debug.log "lt_filter" (filter (\x -> (<) x 3.0) xs)

        _ =
            Debug.log "le_filter" (filter (\x -> (<=) x 3.0) xs)

        _ =
            Debug.log "gt_filter" (filter (\x -> (>) x 3.0) xs)

        _ =
            Debug.log "ge_filter" (filter (\x -> (>=) x 3.0) xs)

        _ =
            Debug.log "count_lt" (countWith (<) 3.0 xs)

        _ =
            Debug.log "count_ge" (countWith (>=) 3.0 xs)
    in
    text "done"
