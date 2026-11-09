module PipelineTest exposing (main)

{-| Tests the pipeline operators `|>` and `<|`: a chain of forward pipes, a
forward pipe into a partially applied local `map`, written with patterns, and
a chain of backward pipes.
-}

-- TAGS: elm-spec, b:Basics.apR, b:Basics.apL, df:infix, d-atexp-op, d-app-closure
-- CHECK: pipe1: 12
-- CHECK: pipe2: [2,4,6]
-- CHECK: backpipe: 10

import Html exposing (text)


double x = x * 2
addOne x = x + 1


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
        _ = Debug.log "pipe1" (5 |> double |> addOne |> addOne)
        _ = Debug.log "pipe2" ([1, 2, 3] |> map double)
        _ = Debug.log "backpipe" (double <| addOne <| 4)
    in
    text "done"
