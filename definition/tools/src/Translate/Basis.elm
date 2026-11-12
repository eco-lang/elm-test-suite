module Translate.Basis exposing (constructor, effectValue, operator, value, valueNames)

{-| The type schemes of the names the Lean environment E0 binds (Basis.lean, InitialBasis.lean),
as Appendix C of A Standard Definition of Elm? gives them (appendix-static-basis.tex): checked by
hand against that appendix on 2026-11-09 (plans/elm-to-lean-translator.md, B.6). A scheme's
quantified variables are numbered -1, -2, ... within the scheme.
-}

import Dict
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

        -- the effect modules (Appendix C, Figures fig:static-basis-platform, fig:static-basis-task and
        -- fig:static-basis-effects; checked by hand against the appendix on 2026-11-11)
        _ ->
            if isEffectModule m then
                effectValue m x

            else
                value0 m x


{-| Whether a qualifier names one of the effect modules (as written, or the default imports'
`Cmd` and `Sub`).
-}
isEffectModule : String -> Bool
isEffectModule m =
    List.member m [ "Platform", "Platform.Cmd", "Platform.Sub", "Cmd", "Sub", "Task", "Process" ]


cmd : Type -> Type
cmd t =
    TCon "Cmd" [ t ]


sub : Type -> Type
sub t =
    TCon "Sub" [ t ]


task : Type -> Type -> Type
task x a =
    TCon "Task" [ x, a ]


unitT : Type
unitT =
    TTuple []


{-| A value of an effect module. -}
effectValue : String -> String -> Maybe Scheme
effectValue m x =
    let
        module_ =
            if m == "Cmd" then
                "Platform.Cmd"

            else if m == "Sub" then
                "Platform.Sub"

            else
                m
    in
    case ( module_, x ) of
        ( "Platform", "worker" ) ->
            -- flags 1, model 2, msg 3
            Just
                (anyScheme 3
                    (fn
                        [ TRecord
                            (Dict.fromList
                                [ ( "init", fn [ v 1 ] (TTuple [ v 2, cmd (v 3) ]) )
                                , ( "update", fn [ v 3, v 2 ] (TTuple [ v 2, cmd (v 3) ]) )
                                , ( "subscriptions", fn [ v 2 ] (sub (v 3)) )
                                ]
                            )
                            Nothing
                        ]
                        (TCon "Program" [ v 1, v 2, v 3 ])
                    )
                )

        ( "Platform.Cmd", "none" ) ->
            Just (anyScheme 1 (cmd (v 1)))

        ( "Platform.Cmd", "batch" ) ->
            Just (anyScheme 1 (fn [ TCon "List" [ cmd (v 1) ] ] (cmd (v 1))))

        ( "Platform.Cmd", "map" ) ->
            Just (anyScheme 2 (fn [ fn [ v 1 ] (v 2), cmd (v 1) ] (cmd (v 2))))

        ( "Platform.Sub", "none" ) ->
            Just (anyScheme 1 (sub (v 1)))

        ( "Platform.Sub", "batch" ) ->
            Just (anyScheme 1 (fn [ TCon "List" [ sub (v 1) ] ] (sub (v 1))))

        ( "Platform.Sub", "map" ) ->
            Just (anyScheme 2 (fn [ fn [ v 1 ] (v 2), sub (v 1) ] (sub (v 2))))

        -- Task: x 1, a 2, then b c d e r
        ( "Task", "succeed" ) ->
            Just (anyScheme 2 (fn [ v 2 ] (task (v 1) (v 2))))

        ( "Task", "fail" ) ->
            Just (anyScheme 2 (fn [ v 1 ] (task (v 1) (v 2))))

        ( "Task", "map" ) ->
            Just (anyScheme 3 (fn [ fn [ v 2 ] (v 3), task (v 1) (v 2) ] (task (v 1) (v 3))))

        ( "Task", "map2" ) ->
            Just (anyScheme 4 (fn [ fn [ v 2, v 3 ] (v 4), task (v 1) (v 2), task (v 1) (v 3) ] (task (v 1) (v 4))))

        ( "Task", "map3" ) ->
            Just (anyScheme 5 (fn [ fn [ v 2, v 3, v 4 ] (v 5), task (v 1) (v 2), task (v 1) (v 3), task (v 1) (v 4) ] (task (v 1) (v 5))))

        ( "Task", "map4" ) ->
            Just
                (anyScheme 6
                    (fn [ fn [ v 2, v 3, v 4, v 5 ] (v 6), task (v 1) (v 2), task (v 1) (v 3), task (v 1) (v 4), task (v 1) (v 5) ]
                        (task (v 1) (v 6))
                    )
                )

        ( "Task", "map5" ) ->
            Just
                (anyScheme 7
                    (fn
                        [ fn [ v 2, v 3, v 4, v 5, v 6 ] (v 7), task (v 1) (v 2), task (v 1) (v 3), task (v 1) (v 4), task (v 1) (v 5), task (v 1) (v 6) ]
                        (task (v 1) (v 7))
                    )
                )

        ( "Task", "sequence" ) ->
            Just (anyScheme 2 (fn [ TCon "List" [ task (v 1) (v 2) ] ] (task (v 1) (TCon "List" [ v 2 ]))))

        ( "Task", "andThen" ) ->
            Just (anyScheme 3 (fn [ fn [ v 2 ] (task (v 1) (v 3)), task (v 1) (v 2) ] (task (v 1) (v 3))))

        -- onError: x 1, y 2, a 3
        ( "Task", "onError" ) ->
            Just (anyScheme 3 (fn [ fn [ v 1 ] (task (v 2) (v 3)), task (v 1) (v 3) ] (task (v 2) (v 3))))

        ( "Task", "mapError" ) ->
            Just (anyScheme 3 (fn [ fn [ v 1 ] (v 2), task (v 1) (v 3) ] (task (v 2) (v 3))))

        -- perform: a 1, msg 2
        ( "Task", "perform" ) ->
            Just (anyScheme 2 (fn [ fn [ v 1 ] (v 2), task (TCon "Never" []) (v 1) ] (cmd (v 2))))

        -- attempt: x 1, a 2, msg 3
        ( "Task", "attempt" ) ->
            Just (anyScheme 3 (fn [ fn [ TCon "Result" [ v 1, v 2 ] ] (v 3), task (v 1) (v 2) ] (cmd (v 3))))

        -- spawn: x 1, y 2, a 3
        ( "Process", "spawn" ) ->
            Just (anyScheme 3 (fn [ task (v 1) (v 3) ] (task (v 2) (TCon "ProcessId" []))))

        ( "Process", "sleep" ) ->
            Just (anyScheme 1 (fn [ float ] (task (v 1) unitT)))

        ( "Process", "kill" ) ->
            Just (anyScheme 1 (fn [ TCon "ProcessId" [] ] (task (v 1) unitT)))

        _ ->
            Nothing


{-| A value of E0 other than those of the effect modules. -}
value0 : String -> String -> Maybe Scheme
value0 m x =
    case ( m, x ) of
        -- the harness Html of the test basis (decision D2): text : String -> Html msg
        ( "Html", "text" ) ->
            Just (anyScheme 1 (fn [ string ] (TCon "Node" [ v 1 ])))

        ( "Html", _ ) ->
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

                "logBase" ->
                    Just (mono (fn [ float, float ] float))

                "degrees" ->
                    Just (mono (fn [ float ] float))

                "radians" ->
                    Just (mono (fn [ float ] float))

                "turns" ->
                    Just (mono (fn [ float ] float))

                "fromPolar" ->
                    Just (mono (fn [ TTuple [ float, float ] ] (TTuple [ float, float ])))

                "toPolar" ->
                    Just (mono (fn [ TTuple [ float, float ] ] (TTuple [ float, float ])))

                "never" ->
                    Just (anyScheme 1 (fn [ TCon "Never" [] ] (v 1)))

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

        "Ok" ->
            Just (anyScheme 2 (fn [ v 2 ] (TCon "Result" [ v 1, v 2 ])))

        "Err" ->
            Just (anyScheme 2 (fn [ v 1 ] (TCon "Result" [ v 1, v 2 ])))

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

{-| The names `value` answers unqualified (and as `Basics.`), for the check against Appendix C
(plans/lean-full-definition/step-07-classify.md, section 6).
-}
valueNames : List String
valueNames =
    [ "compare"
    , "min"
    , "max"
    , "clamp"
    , "not"
    , "xor"
    , "isNaN"
    , "isInfinite"
    , "toFloat"
    , "round"
    , "floor"
    , "ceiling"
    , "truncate"
    , "sqrt"
    , "sin"
    , "cos"
    , "tan"
    , "asin"
    , "acos"
    , "atan"
    , "atan2"
    , "e"
    , "pi"
    , "modBy"
    , "remainderBy"
    , "negate"
    , "abs"
    , "identity"
    , "always"
    , "logBase"
    , "degrees"
    , "radians"
    , "turns"
    , "fromPolar"
    , "toPolar"
    , "never"
    ]
