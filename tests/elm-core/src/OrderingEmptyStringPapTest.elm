module OrderingEmptyStringPapTest exposing (main)

{-| Tests `<`, `<=`, `>`, `>=` and `compare` partially applied to `""` and
passed as functions to a local `map` written with patterns.

Each partial application is mapped over `[ "", "a", "ab" ]`, so `""` is always
the left operand: it compares equal to itself and less than both non-empty
strings.

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
        xs : List String
        xs = [ "", "a", "ab" ]

        _ = Debug.log "ltEmpty" (map ((<) "") xs)
        _ = Debug.log "leEmpty" (map ((<=) "") xs)
        _ = Debug.log "gtEmpty" (map ((>) "") xs)
        _ = Debug.log "geEmpty" (map ((>=) "") xs)
        _ = Debug.log "cmpEmpty" (map (compare "") xs)
    in
    text "done"
