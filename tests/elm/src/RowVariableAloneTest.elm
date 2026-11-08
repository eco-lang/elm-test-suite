module RowVariableAloneTest exposing (main)

{-| A record type's extension variable, written alone, is the record of the other fields.

A Standard Definition of Elm?, rule s-ty-rowvar: a row variable written alone denotes the open
record type with no fields of its own. In `{ r | x : Int } -> r -> Int`, the second argument is
the record of the fields that `r` stands for: `{ y : Int }` when the first is `{ x = 1, y = 2 }`.
<https://elm-test-suite.netlify.app/standard/rules/s-ty-rowvar>

-}

-- TAGS: elm-spec, s-ty-rowvar, s-ty-con
-- CHECK: x: 1
-- CHECK: rest z: "b"

import Html


firstX : { r | x : Int } -> r -> Int
firstX withX _ =
    withX.x


sameRest : { r | x : Int } -> r -> r
sameRest _ rest =
    rest


main =
    let
        _ =
            Debug.log "x" (firstX { x = 1, y = 2 } { y = 3 })

        _ =
            Debug.log "rest z" (sameRest { x = 1, y = 2, z = "a" } { y = 5, z = "b" }).z
    in
    Html.text "done"
