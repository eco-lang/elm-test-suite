module FloatEdgeTest exposing (main)

{-| Float edge cases: `round` on halves, NaN in equality, `min` and `compare`, `truncate` of NaN,
and an Int power beyond 2^32.

Most rows log `Debug.toString` of the result.

  - `round` of plus and minus 0.5, 1.5 and 2.5 rounds halves up, towards positive infinity, also
    inside a list (`map round`).
  - NaN is not equal to itself (`==`, `/=`, also inside `Just` and a list) or to 1.
  - `min 1 nan`, and `min` folded over `[ 1 ]` from NaN by a local `foldl`, give NaN (A48): each
    is checked with `isNaN`, which the book defines, and then by its printed form, which it does
    not (A62), though every implementation prints `NaN`.
  - `compare nan 1` is `GT`, also through a `case` on `compare` (`orderName`) and when the NaN is
    the first element of a tuple or list; `orderName` also gives `LT` and `EQ` for ordinary
    numbers.
  - `truncate nan` is 0.
  - `3 ^ 33` is 5559060566555523, exact as an Int.

That `String.toFloat "1.5"` equals the literal `1.5` is checked by StringToFloatLiteralTest.
-}

-- TAGS: elm-spec, b:Basics.round, b:Basics.eq, b:Basics.neq, b:Basics.min, b:Basics.isNaN, b:Basics.compare, b:Basics.truncate, b:Basics.pow
-- MODE-GUARD: a Char equality must give the same answer as under --optimize
-- NO-SKIP: an edge case every compiler must run
-- CHECK: round 2.5: "3"
-- CHECK: round -2.5: "-2"
-- CHECK: round 0.5: "1"
-- CHECK: round -0.5: "0"
-- CHECK: round 1.5: "2"
-- CHECK: round -1.5: "-1"
-- CHECK: nan == nan: "False"
-- CHECK: nan /= nan: "True"
-- CHECK: 1 /= nan: "True"
-- CHECK: min 1 nan is NaN: "True"
-- CHECK: min 1 nan: "NaN"
-- CHECK: compare nan 1: "GT"
-- CHECK: foldl min is NaN: "True"
-- CHECK: foldl min: "NaN"
-- CHECK: map round: "[-2,0,3]"
-- CHECK: case compare nan 1: "GT"
-- CHECK: case compare 1 2: "LT"
-- CHECK: case compare 2 2: "EQ"
-- CHECK: compare tuple nan: "GT"
-- CHECK: compare list nan: "GT"
-- CHECK: just nan == just nan: "False"
-- CHECK: list nan /= list nan: "True"
-- CHECK: truncate nan: "0"
-- CHECK: pow 3 33: "5559060566555523"

import Html exposing (text)


nan : Float
nan =
    0 / 0


inf : Float
inf =
    1 / 0


show : a -> String
show =
    Debug.toString


{-| Folds `f` over a list from the left, as `List.foldl` does.
-}
foldl : (a -> b -> b) -> b -> List a -> b
foldl f acc xs =
    case xs of
        [] ->
            acc

        x :: rest ->
            foldl f (f x acc) rest


{-| Returns the name of `compare a b`, found by a `case` on the `Order`.
-}
orderName : Float -> Float -> String
orderName a b =
    case compare a b of
        LT ->
            "LT"

        EQ ->
            "EQ"

        GT ->
            "GT"


main =
    let
        _ =
            Debug.log "round 2.5" (show (round 2.5))

        _ =
            Debug.log "round -2.5" (show (round -2.5))

        _ =
            Debug.log "round 0.5" (show (round 0.5))

        _ =
            Debug.log "round -0.5" (show (round -0.5))

        _ =
            Debug.log "round 1.5" (show (round 1.5))

        _ =
            Debug.log "round -1.5" (show (round -1.5))

        _ =
            Debug.log "nan == nan" (show (nan == nan))

        _ =
            Debug.log "nan /= nan" (show (nan /= nan))

        _ =
            Debug.log "1 /= nan" (show (1 /= nan))

        _ =
            Debug.log "min 1 nan is NaN" (show (isNaN (min 1 nan)))

        _ =
            Debug.log "min 1 nan" (show (min 1 nan))

        _ =
            Debug.log "compare nan 1" (show (compare nan 1))

        _ =
            Debug.log "foldl min is NaN" (show (isNaN (foldl min nan [ 1 ])))

        _ =
            Debug.log "foldl min" (show (foldl min nan [ 1 ]))

        _ =
            Debug.log "map round" (show [ round -2.5, round -0.5, round 2.5 ])

        _ =
            Debug.log "case compare nan 1" (orderName nan 1)

        _ =
            Debug.log "case compare 1 2" (orderName 1 2)

        _ =
            Debug.log "case compare 2 2" (orderName 2 2)

        _ =
            Debug.log "compare tuple nan" (show (compare ( nan, 1 ) ( 1, 1 )))

        _ =
            Debug.log "compare list nan" (show (compare [ nan ] [ 1 ]))

        _ =
            Debug.log "just nan == just nan" (show (Just nan == Just nan))

        _ =
            Debug.log "list nan /= list nan" (show ([ nan ] /= [ nan ]))

        _ =
            Debug.log "truncate nan" (show (truncate nan))

        _ =
            Debug.log "pow 3 33" (show (3 ^ 33))
    in
    text "done"
