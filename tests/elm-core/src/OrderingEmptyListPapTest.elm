module OrderingEmptyListPapTest exposing (main)

{-| The operators `<`, `<=`, `>` and `>=` and the function `compare`,
partially applied to the empty list, work as function values passed to
a local `map`, written with patterns, over `[ [], [ 1 ], [ 1, 2 ] ]`.

The empty list is equal to itself and less than any non-empty list.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: ltEmpty: [False,True,True]
-- CHECK: leEmpty: [True,True,True]
-- CHECK: gtEmpty: [False,False,False]
-- CHECK: geEmpty: [True,False,False]
-- CHECK: cmpEmpty: [EQ,LT,LT]

import Html exposing (text)


{-| Applies `f` to each element of a list.
-}
map : (a -> b) -> List a -> List b
map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


main =
    let
        emptyL : List Int
        emptyL = []

        xs : List (List Int)
        xs = [ emptyL, [ 1 ], [ 1, 2 ] ]

        _ = Debug.log "ltEmpty" (map ((<) emptyL) xs)
        _ = Debug.log "leEmpty" (map ((<=) emptyL) xs)
        _ = Debug.log "gtEmpty" (map ((>) emptyL) xs)
        _ = Debug.log "geEmpty" (map ((>=) emptyL) xs)
        _ = Debug.log "cmpEmpty" (map (compare emptyL) xs)
    in
    text "done"
