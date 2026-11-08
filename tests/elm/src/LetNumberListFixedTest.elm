module LetNumberListFixedTest exposing (main)

{-| Both elements of a list of `number` literals, matched by the fixed-length
list pattern `[ a, b ]` and multiplied by a `Float`, are `Float`s.

`case [ 30, 40 ] of [ a, b ] -> round (a * 1.5) + round (b * 1.5)` is 45 + 60,
so the test logs 105.

-}

-- TAGS: elm-spec, s-atexp-scon, d-atexp-scon, d-pat-cons
-- CHECK: listfixed: 105

import Html exposing (text)


main =
    let
        result =
            case [ 30, 40 ] of
                [ a, b ] ->
                    round (a * 1.5) + round (b * 1.5)

                _ ->
                    0

        _ =
            Debug.log "listfixed" result
    in
    text "done"
