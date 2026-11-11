module FloatNaNTest exposing (main)

{-| `isNaN` is True for `0.0 / 0.0` and False for 3.14, and NaN plus 1.0 is NaN: the book's `add`
gives NaN when either argument is NaN.

The last line checks how a NaN is printed. `Debug.log` output is outside the book (A62), but
Elm/JS, Lamdera and eco all print `NaN`, as JavaScript's `Number::toString` does.

-}

-- TAGS: elm-spec, b:Basics.isNaN
-- CHECK: isNaN1: True
-- CHECK: isNaN2: False
-- CHECK: nanProp: True
-- CHECK: nanShown: NaN

import Html exposing (text)


main =
    let
        nan = 0.0 / 0.0
        _ = Debug.log "isNaN1" (isNaN nan)
        _ = Debug.log "isNaN2" (isNaN 3.14)
        _ = Debug.log "nanProp" (isNaN (nan + 1.0))
        _ = Debug.log "nanShown" (nan + 1.0)
    in
    text "done"
