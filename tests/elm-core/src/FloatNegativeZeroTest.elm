module FloatNegativeZeroTest exposing (main)

{-| Negative zero (`-0.0`) equals 0.0, and dividing 1.0 by it gives -Infinity while dividing by 0.0 gives Infinity.
-}

-- TAGS: elm-spec, b:Basics.eq, b:Basics.fdiv, df:negation, b:Basics.negate, df:infix, d-atexp-op, d-exp-app, d-app-basic-partial, d-app-basic-apply, d-atexp-var, d-atexp-paren
-- CHECK: eq: True
-- CHECK: div1: Infinity
-- CHECK: div2: -Infinity

import Html exposing (text)


main =
    let
        negZero = -0.0
        _ = Debug.log "eq" (negZero == 0.0)
        _ = Debug.log "div1" (1.0 / 0.0)
        _ = Debug.log "div2" (1.0 / negZero)
    in
    text "done"
