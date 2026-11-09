module StringToFloatLiteralTest exposing (main)

{-| `String.toFloat "1.5"` gives `Just 1.5`, equal to the literal `1.5`.
-}

-- MODE-GUARD: a Char equality must give the same answer as under --optimize
-- NO-SKIP: an edge case every compiler must run
-- CHECK: toFloat just: Just 1.5
-- CHECK: toFloat just eq: True

import Html exposing (text)


main =
    let
        _ =
            Debug.log "toFloat just" (String.toFloat "1.5")

        _ =
            Debug.log "toFloat just eq" (String.toFloat "1.5" == Just 1.5)
    in
    text "done"
