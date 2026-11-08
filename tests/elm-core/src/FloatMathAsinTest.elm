module FloatMathAsinTest exposing (..)

{-| `asin 0` is 0.
-}

-- TAGS: elm-spec, b:Basics.asin
-- CHECK: testValue: 0

import Basics exposing (..)
import Char exposing (..)
import List exposing (..)
import Maybe exposing (..)
import String exposing (..)
import Html


testValue : Float
testValue =
    Basics.asin 0


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    Html.text "done"
