module NotEqualBoolIfTest exposing (main)

{-| The result of `/=` on two `Bool` literals is used as the condition of an
`if`, for all four combinations of operands; each logs `"yes"` exactly when
the operands differ.
-}

-- TAGS: elm-spec, b:Basics.neq, df:if, d-exp-case, d-match-first, d-match-next, d-mrule-match, d-mrule-fail, d-pat-atpat, d-atpat-con, d-atpat-con-fail, d-atexp-paren, df:infix, d-atexp-op, d-exp-app, d-app-basic-partial, d-app-basic-apply
-- CHECK: ifTT: "no"
-- CHECK: ifTF: "yes"
-- CHECK: ifFT: "yes"
-- CHECK: ifFF: "no"

import Html exposing (text)


main =
    let
        _ = Debug.log "ifTT" (if True /= True then "yes" else "no")
        _ = Debug.log "ifTF" (if True /= False then "yes" else "no")
        _ = Debug.log "ifFT" (if False /= True then "yes" else "no")
        _ = Debug.log "ifFF" (if False /= False then "yes" else "no")
    in
    text "done"
