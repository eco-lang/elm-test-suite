module CombinatorSpMulTest exposing (main)

{-| The SP combinator with operator sections as its functions: `sp (*) ((+) 1) ((*) 2) 6` is `7 * 12`, which is 84.
-}

-- TAGS: elm-spec, d-atexp-op, d-app-basic-partial, d-app-closure, d-app-basic-apply
-- CHECK: result: 84

import Html exposing (text)


sp bf uf1 uf2 x = bf (uf1 x) (uf2 x)


main =
    let
        _ = Debug.log "result" (sp (*) ((+) 1) ((*) 2) 6)
    in
    text "done"
