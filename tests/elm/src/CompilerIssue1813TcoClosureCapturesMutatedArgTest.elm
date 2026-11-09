module CompilerIssue1813TcoClosureCapturesMutatedArgTest exposing (main)

{-| A lambda created in a self tail call keeps the argument value of its own call.

<https://github.com/elm/compiler/issues/1813>

Elm 0.19.1 compiles the tail call into a `while` loop that reassigns `n`, and the closures
`\() -> n` all capture that one variable, so they all return 0. Each closure should return
the `n` of its own call: `[1,2,3]`.

The issue's own program used the library function `List.map` to call the closures; this version
reproduces the same bug with a local `map` in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, d-exp-lambda, d-app-closure
-- CHECK: results: [1,2,3]

import Html exposing (text)


loop : Int -> List (() -> Int) -> List (() -> Int)
loop n list =
    if n <= 0 then
        list

    else
        loop (n - 1) ((\() -> n) :: list)


map : (a -> b) -> List a -> List b
map f list =
    case list of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


main =
    let
        _ =
            Debug.log "results" (map (\f -> f ()) (loop 3 []))
    in
    text "done"
