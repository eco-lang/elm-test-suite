module EqualityBoolPapTest exposing (main)

{-| `(==)` partially applied to a `Bool` works as an ordinary predicate passed
to the local helpers `map`, `filter` and `any`, written with patterns.

`isTrue` is `(==) True` and `isFalse` is `(==) False`. Mapped over `[True,
False, True, False]` they give the list itself and its negation; filtering keeps
the two matching elements; and `any` is `True` for both, since the list
contains each value.

-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: isTrueList: [True,False,True,False]
-- CHECK: isFalseList: [False,True,False,True]
-- CHECK: filterTrue: [True,True]
-- CHECK: filterFalse: [False,False]
-- CHECK: anyTrue: True
-- CHECK: anyFalse: True

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


{-| Whether `p` holds for some element of a list.
-}
any : (a -> Bool) -> List a -> Bool
any p xs =
    case xs of
        [] ->
            False

        x :: rest ->
            p x || any p rest


main =
    let
        isTrue : Bool -> Bool
        isTrue = (==) True

        isFalse : Bool -> Bool
        isFalse = (==) False

        bs : List Bool
        bs = [ True, False, True, False ]

        _ = Debug.log "isTrueList" (map isTrue bs)
        _ = Debug.log "isFalseList" (map isFalse bs)
        _ = Debug.log "filterTrue" (filter isTrue bs)
        _ = Debug.log "filterFalse" (filter isFalse bs)
        _ = Debug.log "anyTrue" (any isTrue bs)
        _ = Debug.log "anyFalse" (any isFalse bs)
    in
    text "done"
