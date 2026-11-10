module Translate.Specialise exposing (CheckKind(..), Specialised, specialise)

{-| Number specialisation (A Standard Definition of Elm?, sec:dynamic-core-numbers; rulings A87,
A27, A93; plans/elm-to-lean-translator.md, B.8). Each declaration whose bindings quantify `number`
variables is replaced by its default copy (every such variable Int, under its own names) and one
copy for each other assignment of Int or Float at which the program uses it, under new names; each
occurrence refers to the copy for its instance; a `number` variable nothing fixes is Int. Copies are
made from the outside in: each scope finds the copies its declarations need by a fixpoint over the
copies already made and its body.
-}

import Dict exposing (Dict)
import Set exposing (Set)
import Translate.Infer as Infer exposing (Inferred)
import Translate.Ir exposing (..)
import Translate.Types as Types exposing (Class(..), Type(..))


type CheckKind
    = KInt
    | KFloat
    | KString
    | KChar
    | KData
    | KFunction


type alias Specialised =
    { program : TestProgram
    , kinds : List CheckKind

    -- whether the program uses a value the Lean kernel cannot compute (`nativeValues`)
    , native : Bool
    }


type Num
    = IntN
    | FloatN


type alias Assignment =
    List ( Int, Num )


key : Assignment -> String
key a =
    a
        |> List.map
            (\( _, n ) ->
                case n of
                    IntN ->
                        "Int"

                    FloatN ->
                        "Float"
            )
        |> String.join "$"


isDefault : Assignment -> Bool
isDefault =
    List.all (\( _, n ) -> n == IntN)


copyName : String -> Assignment -> String
copyName name a =
    if isDefault a then
        name

    else
        name ++ "$" ++ key a


type alias Request =
    { group : Int, assignment : Assignment }


type alias Ctx =
    { inferred : Inferred
    , rho : Dict Int Num
    , own : Dict Int Assignment
    }


{-| A type read as Int or Float under the assignments of the enclosing copies; a `number` variable
they do not fix is Int.
-}
resolve : Ctx -> Type -> Result String Num
resolve ctx t =
    case Types.apply ctx.inferred.subst t of
        TCon "Int" [] ->
            Ok IntN

        TCon "Float" [] ->
            Ok FloatN

        TVar v ->
            case Dict.get v ctx.rho of
                Just n ->
                    Ok n

                Nothing ->
                    if Types.classOf ctx.inferred.subst v == Number then
                        Ok IntN

                    else
                        Err ("a number of unknown type (variable " ++ String.fromInt v ++ ")")

        other ->
            Err ("not a number: " ++ Types.show ctx.inferred.subst other)


groupOf : Ctx -> Int -> Maybe ( Int, List Int )
groupOf ctx binder =
    Dict.get binder ctx.inferred.groupKey
        |> Maybe.map (\g -> ( g, Dict.get g ctx.inferred.groupVars |> Maybe.withDefault [] ))


combine : List (Result e a) -> Result e (List a)
combine =
    List.foldr (Result.map2 (::)) (Ok [])


{-| An occurrence of a declared variable: the copy it refers to, and the request for that copy.
-}
occurrence : Ctx -> Int -> Name -> Result String ( Name, List Request )
occurrence ctx occ name =
    case name of
        Local id x ->
            case groupOf ctx id of
                Nothing ->
                    Ok ( name, [] )

                Just ( g, vars ) ->
                    let
                        instance =
                            Dict.get occ ctx.inferred.occurrences |> Maybe.map .instance |> Maybe.withDefault Dict.empty

                        assignment =
                            if List.isEmpty vars then
                                Ok []

                            else if Dict.isEmpty instance then
                                -- inside the binder's own group: the same copy
                                Ok (Dict.get g ctx.own |> Maybe.withDefault (List.map (\v -> ( v, IntN )) vars))

                            else
                                vars
                                    |> List.map
                                        (\v ->
                                            case Dict.get v instance of
                                                Just t ->
                                                    resolve ctx t |> Result.map (\n -> ( v, n ))

                                                Nothing ->
                                                    Ok ( v, IntN )
                                        )
                                    |> combine
                    in
                    assignment
                        |> Result.map (\a -> ( Local id (copyName x a), [ { group = g, assignment = a } ] ))

        Global m x ->
            -- the Elm texts of the basis are specialised too: `abs` used at Float is its copy at Float
            if x == "abs" then
                case Dict.get occ ctx.inferred.occurrences |> Maybe.andThen (.instance >> Dict.values >> List.head) of
                    Just t ->
                        resolve ctx t
                            |> Result.map
                                (\n ->
                                    if n == FloatN then
                                        ( Global m "abs$Float", [] )

                                    else
                                        ( name, [] )
                                )

                    Nothing ->
                        Ok ( name, [] )

            else
                Ok ( name, [] )

        _ ->
            Ok ( name, [] )


{-| An operator, renamed `^@Float` when it is `^` at Float: the same operator of OT_dyn, marked
because its value, the C library's power, is one the Lean kernel cannot compute (`native`).
-}
operatorAt : Ctx -> Int -> String -> Result String String
operatorAt ctx occ op =
    if op == "^" then
        case Dict.get occ ctx.inferred.occurrences |> Maybe.andThen (.instance >> Dict.values >> List.head) of
            Just t ->
                resolve ctx t
                    |> Result.andThen
                        (\n ->
                            if n == FloatN then
                                Ok floatPow

                            else
                                Ok op
                        )

            Nothing ->
                Ok op

    else
        Ok op


floatPow : String
floatPow =
    "^@Float"


{-| The values of the basis whose results only the C library computes (Float.floor and the
elementary functions, Float printing), which the Lean kernel cannot reduce: a program that uses one
is checked by `native_decide` only, with no `decide +kernel` theorem.
-}
nativeValues : Set ( String, String )
nativeValues =
    Set.fromList
        (( "Debug", "toString" )
            :: List.concatMap (\x -> [ ( "", x ), ( "Basics", x ) ])
                [ "round", "floor", "ceiling", "truncate", "sin", "cos", "tan", "asin", "acos", "atan", "atan2" ]
        )


isNative : Expr -> Bool
isNative e =
    case e of
        EVar _ (Global m x) ->
            Set.member ( m, x ) nativeValues

        EBinop _ op _ _ ->
            op == floatPow

        EOp _ op ->
            op == floatPow

        _ ->
            False


type alias Out a =
    Result String ( a, List Request )


map2 : (a -> b -> c) -> Out a -> Out b -> Out c
map2 f a b =
    Result.map2 (\( x, rx ) ( y, ry ) -> ( f x y, rx ++ ry )) a b


list : List (Out a) -> Out (List a)
list =
    List.foldr (map2 (::)) (Ok ( [], [] ))


expr : Ctx -> Expr -> Out Expr
expr ctx e =
    case e of
        EApp f args ->
            map2 EApp (expr ctx f) (list (List.map (expr ctx) args))

        EBinop occ op a b ->
            operatorAt ctx occ op
                |> Result.andThen (\op2 -> map2 (EBinop occ op2) (expr ctx a) (expr ctx b))

        EOp occ op ->
            operatorAt ctx occ op |> Result.map (\op2 -> ( EOp occ op2, [] ))

        EVar occ name ->
            occurrence ctx occ name |> Result.map (\( n, rs ) -> ( EVar occ n, rs ))

        EIf arms final ->
            map2 EIf
                (list (List.map (\( c, t ) -> map2 Tuple.pair (expr ctx c) (expr ctx t)) arms))
                (expr ctx final)

        EInt id digits ->
            case Dict.get id ctx.inferred.literals of
                Just t ->
                    resolve ctx t |> Result.map (\n -> ( EIntAt (n == FloatN) digits, [] ))

                Nothing ->
                    Err "a literal without a type"

        ENeg x ->
            expr ctx x |> Result.map (Tuple.mapFirst ENeg)

        ETuple xs ->
            list (List.map (expr ctx) xs) |> Result.map (Tuple.mapFirst ETuple)

        EParen x ->
            expr ctx x |> Result.map (Tuple.mapFirst EParen)

        ELet decls body ->
            scope ctx decls (\c -> expr c body)
                |> Result.map (\( ( ds, b ), rs ) -> ( ELet ds b, rs ))

        ECase s rules ->
            map2 ECase (expr ctx s) (list (List.map (\( p, b ) -> expr ctx b |> Result.map (Tuple.mapFirst (Tuple.pair p))) rules))

        ELam ps body ->
            expr ctx body |> Result.map (Tuple.mapFirst (ELam ps))

        ERecord fields ->
            list (List.map (\( f, x ) -> expr ctx x |> Result.map (Tuple.mapFirst (Tuple.pair f))) fields)
                |> Result.map (Tuple.mapFirst ERecord)

        EList xs ->
            list (List.map (expr ctx) xs) |> Result.map (Tuple.mapFirst EList)

        EAccess x f ->
            expr ctx x |> Result.map (Tuple.mapFirst (\y -> EAccess y f))

        EUpdate occ name fields ->
            map2 (\( n, _ ) fs -> EUpdate occ n fs)
                (occurrence ctx occ name |> Result.map (\( n, rs ) -> ( ( n, () ), rs )))
                (list (List.map (\( f, x ) -> expr ctx x |> Result.map (Tuple.mapFirst (Tuple.pair f))) fields))

        _ ->
            Ok ( e, [] )


renamePattern : Assignment -> Pattern -> Result String Pattern
renamePattern a p =
    let
        go q =
            case q of
                PVar x id ->
                    Ok (PVar (copyName x a) id)

                PAs inner x id ->
                    go inner |> Result.map (\i -> PAs i (copyName x a) id)

                PTuple ps ->
                    combine (List.map go ps) |> Result.map PTuple

                PCons x y ->
                    Result.map2 PCons (go x) (go y)

                PList ps ->
                    combine (List.map go ps) |> Result.map PList

                PCon n ps ->
                    combine (List.map go ps) |> Result.map (PCon n)

                PParen inner ->
                    go inner |> Result.map PParen

                PRecord fields ->
                    if isDefault a then
                        Ok (PRecord fields)

                    else
                        Err "a record pattern binding that needs a copy at Float"

                _ ->
                    Ok q
    in
    go p


{-| The copy of a declaration for an assignment of its group's `number` variables.
-}
copy : Ctx -> Assignment -> Decl -> Out Decl
copy ctx a d =
    case d of
        DFn f ->
            expr ctx f.body
                |> Result.map (\( body, rs ) -> ( DFn { f | name = copyName f.name a, body = body }, rs ))

        DPat p x ->
            Result.map2 (\q ( y, rs ) -> ( DPat q y, rs )) (renamePattern a p) (expr ctx x)


{-| A scope: its declarations, specialised, and its body (translated by `body` under the scope's
context). Requests for this scope's groups are met here; the others are passed outwards.
-}
scope : Ctx -> List Decl -> (Ctx -> Out b) -> Out ( List Decl, b )
scope ctx decls body =
    let
        indexed =
            dictOfList decls

        comps =
            Infer.components decls

        groupKeyOf cmp =
            cmp
                |> List.concatMap (\i -> Dict.get i indexed |> Maybe.map declBinders |> Maybe.withDefault [])
                |> List.filterMap (\( _, id ) -> Dict.get id ctx.inferred.groupKey)
                |> List.head

        groups =
            comps
                |> List.indexedMap
                    (\n cmp ->
                        let
                            g =
                                groupKeyOf cmp

                            vars =
                                g |> Maybe.andThen (\k -> Dict.get k ctx.inferred.groupVars) |> Maybe.withDefault []
                        in
                        { cmp = cmp, group = g, gid = Maybe.withDefault (-(n + 1)) g, default = List.map (\v -> ( v, IntN )) vars }
                    )

        local =
            groups |> List.filterMap .group |> Set.fromList

        translateCopy grp a =
            let
                inner =
                    { ctx
                        | rho = List.foldl (\( v, n ) r -> Dict.insert v n r) ctx.rho a
                        , own =
                            case grp.group of
                                Just g ->
                                    Dict.insert g a ctx.own

                                Nothing ->
                                    ctx.own
                    }
            in
            list (List.filterMap (\i -> Dict.get i indexed |> Maybe.map (copy inner a)) grp.cmp)

        -- the fixpoint: needed copies by group, the translations made, requests passed outwards
        loop needed made outward =
            let
                pending =
                    groups
                        |> List.concatMap
                            (\grp ->
                                Dict.get grp.gid needed
                                    |> Maybe.withDefault [ grp.default ]
                                    |> List.filter (\a -> not (Dict.member ( grp.gid, key a ) made))
                                    |> List.map (Tuple.pair grp)
                            )
            in
            if List.isEmpty pending then
                Ok ( needed, made, outward )

            else
                pending
                    |> List.foldl
                        (\( grp, a ) acc ->
                            acc
                                |> Result.andThen
                                    (\( nd, md, out ) ->
                                        translateCopy grp a
                                            |> Result.map
                                                (\( ds, rs ) ->
                                                    let
                                                        ( mine, others ) =
                                                            List.partition (\r -> Set.member r.group local) rs
                                                    in
                                                    ( addRequests mine nd
                                                    , Dict.insert ( grp.gid, key a ) ds md
                                                    , out ++ others
                                                    )
                                                )
                                    )
                        )
                        (Ok ( needed, made, outward ))
                    |> Result.andThen (\( nd, md, out ) -> loop nd md out)

        initialNeeded =
            groups
                |> List.filterMap (\grp -> grp.group |> Maybe.map (\g -> ( g, [ grp.default ] )))
                |> Dict.fromList
    in
    body ctx
        |> Result.andThen
            (\( b, bodyRequests ) ->
                let
                    ( mine, others ) =
                        List.partition (\r -> Set.member r.group local) bodyRequests
                in
                loop (addRequests mine initialNeeded) Dict.empty others
                    |> Result.map
                        (\( needed, made, outward ) ->
                            let
                                emitted =
                                    groups
                                        |> List.concatMap
                                            (\grp ->
                                                let
                                                    g =
                                                        grp.gid

                                                    assignments =
                                                        Dict.get g needed
                                                            |> Maybe.withDefault [ grp.default ]
                                                            |> List.sortBy (\a -> ( if isDefault a then 0 else 1, key a ))
                                                in
                                                List.concatMap (\a -> Dict.get ( g, key a ) made |> Maybe.withDefault []) assignments
                                            )
                            in
                            ( ( emitted, b ), outward )
                        )
            )


addRequests : List Request -> Dict Int (List Assignment) -> Dict Int (List Assignment)
addRequests rs needed =
    List.foldl
        (\r d ->
            let
                existing =
                    Dict.get r.group d |> Maybe.withDefault []
            in
            if List.any (\a -> key a == key r.assignment) existing then
                d

            else
                Dict.insert r.group (existing ++ [ r.assignment ]) d
        )
        needed
        rs


dictOfList : List a -> Dict Int a
dictOfList xs =
    Dict.fromList (List.indexedMap Tuple.pair xs)


kindOf : Ctx -> Type -> CheckKind
kindOf ctx t =
    case Types.apply ctx.inferred.subst t of
        TCon "Int" [] ->
            KInt

        TCon "Float" [] ->
            KFloat

        TCon "String" [] ->
            KString

        TCon "Char" [] ->
            KChar

        TFun _ _ ->
            KFunction

        TVar v ->
            if Types.classOf ctx.inferred.subst v == Number then
                KInt

            else
                KData

        _ ->
            KData


specialise : TestProgram -> Inferred -> Result String Specialised
specialise program inferred =
    let
        ctx =
            { inferred = inferred, rho = Dict.empty, own = Dict.empty }

        checksOf c =
            list (List.map (\ch -> expr c ch.expr |> Result.map (Tuple.mapFirst (\x -> { ch | expr = x }))) program.checks)

        mainScope c =
            scope c program.locals checksOf
    in
    scope ctx program.defs mainScope
        |> Result.map
            (\( ( defs, ( locals, checks ) ), _ ) ->
                { program = { program | defs = defs, locals = locals, checks = checks }
                , kinds = List.map (kindOf ctx) inferred.checkTypes
                , native =
                    List.any (anyExpr isNative)
                        (List.concatMap declExprs (defs ++ locals) ++ List.map .expr checks)
                }
            )


declExprs : Decl -> List Expr
declExprs d =
    case d of
        DFn f ->
            [ f.body ]

        DPat _ x ->
            [ x ]
