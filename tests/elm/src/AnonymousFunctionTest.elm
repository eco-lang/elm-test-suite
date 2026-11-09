module AnonymousFunctionTest exposing (main)

{-| Anonymous functions work as the function argument of higher-order functions.

The program passes lambdas to local `map`, `foldl` and `filter` functions written by pattern
matching on lists.

-}

-- TAGS: elm-spec, s-exp-lambda, d-exp-lambda, d-app-closure
-- CHECK: lambda1: [2,4,6]
-- CHECK: lambda2: 15
-- CHECK: lambda3: [2,4]

import Html exposing (text)


map : (a -> b) -> List a -> List b
map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


foldl : (a -> b -> b) -> b -> List a -> b
foldl f acc xs =
    case xs of
        [] ->
            acc

        x :: rest ->
            foldl f (f x acc) rest


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
        _ = Debug.log "lambda1" (map (\x -> x * 2) [1, 2, 3])
        _ = Debug.log "lambda2" (foldl (\x acc -> x + acc) 0 [1, 2, 3, 4, 5])
        _ = Debug.log "lambda3" (filter (\x -> modBy 2 x == 0) [1, 2, 3, 4, 5])
    in
    text "done"
