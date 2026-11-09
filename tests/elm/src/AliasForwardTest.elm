module AliasForwardTest exposing (main)

{-| Top-level values defined as another function, `dup = twice` and `plus = (+)`, behave like the function they name.

`dup` is called at `Int` and at `String` and is passed as a value to a
local `map`. `plus` is called fully applied through `inc`, passed to a local
`foldl` at `Int` and at `Float`, and partially applied in `map`. The `Float`
result is reduced to an `Int` before it is logged.

-}

import Html exposing (text)



-- TAGS: elm-spec, sm-topdec-value, s-valbind-var, s-atexp-op, d-atexp-op, d-app-basic-partial, d-app-basic-apply
-- CHECK: dupInt: 3
-- CHECK: dupStr: "a!!"
-- CHECK: foldInt: 6
-- CHECK: foldFloat: 45
-- CHECK: mapPartial: 5
-- CHECK: value: 4


twice : (a -> a) -> a -> a
twice f x =
    f (f x)


dup : (a -> a) -> a -> a
dup =
    twice


plus : number -> number -> number
plus =
    (+)


inc : Int -> Int
inc n =
    plus n 1


bang : String -> String
bang s =
    s ++ "!"


foldl : (a -> b -> b) -> b -> List a -> b
foldl f acc xs =
    case xs of
        [] ->
            acc

        x :: rest ->
            foldl f (f x acc) rest


map : (a -> b) -> List a -> List b
map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


sum : List number -> number
sum xs =
    foldl (+) 0 xs


main =
    let
        _ =
            Debug.log "dupInt" (dup inc 1)

        _ =
            Debug.log "dupStr" (dup bang "a")

        _ =
            Debug.log "foldInt" (foldl plus 0 [ 1, 2, 3 ])

        _ =
            Debug.log "foldFloat" (round (foldl plus 0.5 [ 1.5, 2.5 ] * 10))

        _ =
            Debug.log "mapPartial" (sum (map (plus 1) [ 1, 2 ]))

        _ =
            Debug.log "value" (sum (map dup [ inc ] |> map (\g -> g 2)))
    in
    text "done"
