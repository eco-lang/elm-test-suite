module ListConsFloatTest exposing (main)

{-| A `List Float` literal holds its numbers in order, and `::` prepends a number to it.

The test prints the list, its head (read with a `case`), and the list with `0.0` consed onto the front. `Debug.log` prints the whole-number floats `1.0` and `0.0` as `1` and `0`.

-}

-- TAGS: elm-spec, s-atexp-op, d-app-con
-- CHECK: list: [1,2.5,3.75]
-- CHECK: head: Just 1
-- CHECK: prepend: [0,1,2.5,3.75]


import Html exposing (text)


main =
    let
        xs : List Float
        xs =
            [ 1.0, 2.5, 3.75 ]

        _ =
            Debug.log "list" xs

        _ =
            Debug.log "head"
                (case xs of
                    h :: _ ->
                        Just h

                    [] ->
                        Nothing
                )

        _ =
            Debug.log "prepend" (0.0 :: xs)
    in
    text "done"
