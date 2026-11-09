module EqualityBoolIfTest exposing (main)

{-| The result of `==` and `/=` on `Bool` operands drives an `if` expression
correctly.

All four `==` comparisons of `True` and `False` choose `"yes"` exactly when the
operands are equal. The two `/=` cases choose `"yes"` only for `True /= False`.

-}

-- TAGS: elm-spec, b:Basics.eq, b:Basics.neq, df:if, d-exp-case, d-match-first, d-match-next, d-mrule-match, d-mrule-fail, d-pat-atpat, d-atpat-con, d-atpat-con-fail, d-atexp-paren, df:infix, d-atexp-op, d-exp-app, d-app-basic-partial, d-app-basic-apply
-- CHECK: ifTT: "yes"
-- CHECK: ifTF: "no"
-- CHECK: ifFT: "no"
-- CHECK: ifFF: "yes"
-- CHECK: nifTT: "no"
-- CHECK: nifTF: "yes"

import Html exposing (text)


main =
    let
        _ = Debug.log "ifTT" (if True == True then "yes" else "no")
        _ = Debug.log "ifTF" (if True == False then "yes" else "no")
        _ = Debug.log "ifFT" (if False == True then "yes" else "no")
        _ = Debug.log "ifFF" (if False == False then "yes" else "no")
        _ = Debug.log "nifTT" (if True /= True then "yes" else "no")
        _ = Debug.log "nifTF" (if True /= False then "yes" else "no")
    in
    text "done"
