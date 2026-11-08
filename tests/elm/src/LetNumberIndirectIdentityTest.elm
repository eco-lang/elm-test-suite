module LetNumberIndirectIdentityTest exposing (main)

{-| A let-bound `number` passed through `identity` before a `Float`
multiplication is a `Float`.

With `n = 30`, `round (identity n * 1.5)` logs 45.

-}

-- TAGS: elm-spec, s-dec-group, s-atexp-scon, d-atexp-scon
-- CHECK: identity: 45

import Html exposing (text)


main =
    let
        identityN =
            let
                n =
                    30
            in
            round (identity n * 1.5)

        _ =
            Debug.log "identity" identityN
    in
    text "done"
