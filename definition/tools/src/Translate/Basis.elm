module Translate.Basis exposing (constructor, operator, value)

{-| The type schemes of the names the Lean environment E0 binds (Basis.lean, InitialBasis.lean),
as Appendix C of A Standard Definition of Elm? gives them (appendix-static-basis.tex): checked by
hand against that appendix on 2026-11-09 (plans/elm-to-lean-translator.md, B.6). A scheme's
quantified variables are numbered -1, -2, ... within the scheme.
-}

import Translate.Types exposing (Class(..), Scheme, Type(..))


{-| The n-th variable of a scheme. Scheme variables are negative, so that they never meet the
inference's own variables, which are positive.
-}
v : Int -> Type
v n =
    TVar (negate n)


fn : List Type -> Type -> Type
fn args result =
    List.foldr TFun result args


int : Type
int =
    TCon "Int" []


float : Type
float =
    TCon "Float" []


bool : Type
bool =
    TCon "Bool" []


order : Type
order =
    TCon "Order" []


string : Type
string =
    TCon "String" []


char : Type
char =
    TCon "Char" []


{-| append, and `++`: forall appendable. appendable -> appendable -> appendable.
-}
appendScheme : Scheme
appendScheme =
    { quantified = [ ( -1, Appendable ) ], t = fn [ v 1, v 1 ] (v 1) }


mono : Type -> Scheme
mono t =
    { quantified = [], t = t }


numberScheme : Type -> Scheme
numberScheme t =
    { quantified = [ ( -1, Number ) ], t = t }


comparableScheme : Type -> Scheme
comparableScheme t =
    { quantified = [ ( -1, Comparable ) ], t = t }


anyScheme : Int -> Type -> Scheme
anyScheme n t =
    { quantified = List.map (\i -> ( negate i, Any )) (List.range 1 n), t = t }


{-| A value of E0, by its module ("" for unqualified, or "Basics", "Debug", "Char") and name.
-}
value : String -> String -> Maybe Scheme
value m x =
    case ( m, x ) of
        ( "Debug", "log" ) ->
            Just (anyScheme 1 (fn [ string, v 1 ] (v 1)))

        ( "Debug", "todo" ) ->
            Just (anyScheme 1 (fn [ string ] (v 1)))

        ( "Debug", "toString" ) ->
            Just (anyScheme 1 (fn [ v 1 ] string))

        ( "Debug", _ ) ->
            Nothing

        ( "Char", "toCode" ) ->
            Just (mono (fn [ char ] int))

        ( "Char", "fromCode" ) ->
            Just (mono (fn [ int ] char))

        ( "Char", _ ) ->
            Nothing

        _ ->
            case x of
                "compare" ->
                    Just (comparableScheme (fn [ v 1, v 1 ] order))

                "min" ->
                    Just (comparableScheme (fn [ v 1, v 1 ] (v 1)))

                "max" ->
                    Just (comparableScheme (fn [ v 1, v 1 ] (v 1)))

                "clamp" ->
                    Just (numberScheme (fn [ v 1, v 1, v 1 ] (v 1)))

                "not" ->
                    Just (mono (fn [ bool ] bool))

                "xor" ->
                    Just (mono (fn [ bool, bool ] bool))

                "isNaN" ->
                    Just (mono (fn [ float ] bool))

                "isInfinite" ->
                    Just (mono (fn [ float ] bool))

                "toFloat" ->
                    Just (mono (fn [ int ] float))

                "round" ->
                    Just (mono (fn [ float ] int))

                "floor" ->
                    Just (mono (fn [ float ] int))

                "ceiling" ->
                    Just (mono (fn [ float ] int))

                "truncate" ->
                    Just (mono (fn [ float ] int))

                "sqrt" ->
                    Just (mono (fn [ float ] float))

                "sin" ->
                    Just (mono (fn [ float ] float))

                "cos" ->
                    Just (mono (fn [ float ] float))

                "tan" ->
                    Just (mono (fn [ float ] float))

                "asin" ->
                    Just (mono (fn [ float ] float))

                "acos" ->
                    Just (mono (fn [ float ] float))

                "atan" ->
                    Just (mono (fn [ float ] float))

                "atan2" ->
                    Just (mono (fn [ float, float ] float))

                "e" ->
                    Just (mono float)

                "pi" ->
                    Just (mono float)

                "append" ->
                    Just appendScheme

                "modBy" ->
                    Just (mono (fn [ int, int ] int))

                "remainderBy" ->
                    Just (mono (fn [ int, int ] int))

                "negate" ->
                    Just (numberScheme (fn [ v 1 ] (v 1)))

                "abs" ->
                    Just (numberScheme (fn [ v 1 ] (v 1)))

                "identity" ->
                    Just (anyScheme 1 (fn [ v 1 ] (v 1)))

                "always" ->
                    Just (anyScheme 2 (fn [ v 1, v 2 ] (v 1)))

                _ ->
                    Nothing


{-| A constructor of E0 (`True`, `LT`, `Just`, ...), unqualified or qualified.
-}
constructor : String -> Maybe Scheme
constructor k =
    case k of
        "True" ->
            Just (mono bool)

        "False" ->
            Just (mono bool)

        "LT" ->
            Just (mono order)

        "EQ" ->
            Just (mono order)

        "GT" ->
            Just (mono order)

        "Just" ->
            Just (anyScheme 1 (fn [ v 1 ] (TCon "Maybe" [ v 1 ])))

        "Nothing" ->
            Just (anyScheme 1 (TCon "Maybe" [ v 1 ]))

        _ ->
            Nothing


{-| An operator of the dynamic operator table, OT_dyn.
-}
operator : String -> Maybe Scheme
operator op =
    if List.member op [ "+", "-", "*", "^" ] then
        Just (numberScheme (fn [ v 1, v 1 ] (v 1)))

    else if op == "/" then
        Just (mono (fn [ float, float ] float))

    else if op == "//" then
        Just (mono (fn [ int, int ] int))

    else if op == "==" || op == "/=" then
        Just (anyScheme 1 (fn [ v 1, v 1 ] bool))

    else if List.member op [ "<", ">", "<=", ">=" ] then
        Just (comparableScheme (fn [ v 1, v 1 ] bool))

    else if op == "&&" || op == "||" then
        Just (mono (fn [ bool, bool ] bool))

    else if op == "++" then
        Just appendScheme

    else if op == "::" then
        Just (anyScheme 1 (fn [ v 1, TCon "List" [ v 1 ] ] (TCon "List" [ v 1 ])))

    else if op == "<<" then
        Just (anyScheme 3 (fn [ fn [ v 2 ] (v 3), fn [ v 1 ] (v 2), v 1 ] (v 3)))

    else if op == ">>" then
        Just (anyScheme 3 (fn [ fn [ v 1 ] (v 2), fn [ v 2 ] (v 3), v 1 ] (v 3)))

    else if op == "|>" then
        Just (anyScheme 2 (fn [ v 1, fn [ v 1 ] (v 2) ] (v 2)))

    else if op == "<|" then
        Just (anyScheme 2 (fn [ fn [ v 1 ] (v 2), v 1 ] (v 2)))

    else
        Nothing
