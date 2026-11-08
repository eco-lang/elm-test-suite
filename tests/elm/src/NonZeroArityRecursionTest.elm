module NonZeroArityRecursionTest exposing (main)

{-| A self-recursive top-level function, `countDown : Int -> Int`, calls
itself in tail position from 100 down to 0 and returns 0; the program logs
`countDown: 0`.
-}

-- TAGS: elm-spec, sm-topdec-value, dm-topdec-val
-- CHECK: countDown: 0

import Html exposing (text)


countDown : Int -> Int
countDown n =
    if n <= 0 then
        0

    else
        countDown (n - 1)


main =
    let
        _ =
            Debug.log "countDown" (countDown 100)
    in
    text "done"
