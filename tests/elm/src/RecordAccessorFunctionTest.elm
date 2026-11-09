module RecordAccessorFunctionTest exposing (main)

{-| Record accessor functions such as `.name` work as arguments to a function.

`main` maps `.name` over two people records and `.x` over two point records, with
a local `map`.
-}

-- TAGS: elm-spec, s-atpat-record, d-atpat-record, d-patrow-field
-- CHECK: names: ["Alice","Bob"]
-- CHECK: xs: [1,4]

import Html exposing (text)


map : (a -> b) -> List a -> List b
map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


main =
    let
        people = [ { name = "Alice", age = 30 }, { name = "Bob", age = 25 } ]
        points = [ { x = 1, y = 2 }, { x = 4, y = 5 } ]
        _ = Debug.log "names" (map .name people)
        _ = Debug.log "xs" (map .x points)
    in
    text "done"
