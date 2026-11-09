module NotEqualBoolPapTest exposing (main)

{-| `(/=)` partially applied to a `Bool`, as `(/=) True` and `(/=) False`,
works as a function value passed to the local helpers `map`, `filter` and
`any`, written with patterns, over `[ True, False, True, False ]`.
-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: isNotTrueList: [False,True,False,True]
-- CHECK: isNotFalseList: [True,False,True,False]
-- CHECK: filterNotTrue: [False,False]
-- CHECK: filterNotFalse: [True,True]
-- CHECK: anyNotTrue: True
-- CHECK: anyNotFalse: True

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
        isNotTrue : Bool -> Bool
        isNotTrue = (/=) True

        isNotFalse : Bool -> Bool
        isNotFalse = (/=) False

        bs : List Bool
        bs = [ True, False, True, False ]

        _ = Debug.log "isNotTrueList" (map isNotTrue bs)
        _ = Debug.log "isNotFalseList" (map isNotFalse bs)
        _ = Debug.log "filterNotTrue" (filter isNotTrue bs)
        _ = Debug.log "filterNotFalse" (filter isNotFalse bs)
        _ = Debug.log "anyNotTrue" (any isNotTrue bs)
        _ = Debug.log "anyNotFalse" (any isNotFalse bs)
    in
    text "done"
