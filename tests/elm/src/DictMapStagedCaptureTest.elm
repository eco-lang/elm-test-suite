module DictMapStagedCaptureTest exposing (main)

{-| A two-argument function passed as a parameter and applied to both of its
arguments inside a lambda that a mapping function calls with two arguments
receives both of them.

The function passed is `makeAdder`, whose definition takes one argument and
returns a lambda for the second. The dictionary is a list of key-value pairs,
and `mapValues` calls its function with each key and value, as `Dict.map` does.
`mapTupleDict` hands it a lambda over values that are `( Int, Int )` pairs; the
lambda destructures each pair and calls `makeAdder` with both parts. 10 and 20
become 15 and 27.

The program keeps to A Standard Definition of Elm?'s basis: an earlier version
used `Dict` and `String.length`, which lie outside the definition.

-}

-- TAGS: elm-spec, d-app-closure, d-exp-lambda, d-atpat-tuple
-- CHECK: result: [("a",(5,15)),("b",(7,27))]

import Html exposing (text)


{-| Returns a function adding `width` to its argument.
-}
makeAdder : Int -> (Int -> Int)
makeAdder width =
    \value -> width + value


{-| Applies `f` to each key and value of `pairs`, keeping the keys.
-}
mapValues : (k -> v -> w) -> List ( k, v ) -> List ( k, w )
mapValues f pairs =
    case pairs of
        [] ->
            []

        ( k, v ) :: rest ->
            ( k, f k v ) :: mapValues f rest


{-| Replaces the second `Int` in each value `( width, value )` of `dict` with
`alter width value`.
-}
mapTupleDict : (Int -> Int -> Int) -> List ( String, ( Int, Int ) ) -> List ( String, ( Int, Int ) )
mapTupleDict alter dict =
    mapValues (\_ ( width, value ) -> ( width, alter width value )) dict


main =
    let
        d =
            [ ( "a", ( 5, 10 ) )
            , ( "b", ( 7, 20 ) )
            ]

        result =
            mapTupleDict makeAdder d

        _ =
            Debug.log "result" result
    in
    text "done"
