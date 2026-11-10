module Translate.Infer exposing
    ( Inferred
    , Occurrence
    , components
    , freeLocals
    , infer
    )

{-| Type inference over a translated program (plans/elm-to-lean-translator.md, B.7): Hindley-Milner
with let-polymorphism, the classes of Standard Elm, and records with rows. Declarations are inferred
component by component (the "refers to" grouping of Appendix A, as `Derived.lean`'s `components`
computes it), each component generalised before the next; a component is closed as one, every
binding over all the component's `number` variables (ruling A93).

What it records is what number specialisation needs: the type of every integer literal, the
instance at which every occurrence uses a declaration, the `number` variables of every group, and
the type of every check.

-}

import Dict exposing (Dict)
import Elm.Syntax.Node as Node exposing (Node(..))
import Elm.Syntax.TypeAnnotation as T
import Set exposing (Set)
import Translate.Basis as Basis
import Translate.Ir exposing (..)
import Translate.Types as Types exposing (Class(..), Scheme, Subst, Type(..))


type alias Occurrence =
    { binder : Int, instance : Dict Int Type }


type alias Inferred =
    { subst : Subst
    , literals : Dict Int Type
    , occurrences : Dict Int Occurrence
    , groupKey : Dict Int Int
    , groupVars : Dict Int (List Int)
    , checkTypes : List Type
    }


type alias St =
    { subst : Subst
    , literals : Dict Int Type
    , occurrences : Dict Int Occurrence
    , groupKey : Dict Int Int
    , groupVars : Dict Int (List Int)
    }


type alias Env =
    { values : Dict Int Scheme
    , annVars : Dict String Type
    , program : TestProgram
    , cons : Dict String Scheme
    }


type alias R a =
    Result String ( a, St )


fresh : Class -> St -> ( Type, St )
fresh cls st =
    let
        ( t, s ) =
            Types.freshVar cls st.subst
    in
    ( t, { st | subst = s } )


unify : Type -> Type -> St -> Result String St
unify a b st =
    Types.unify a b st.subst |> Result.map (\s -> { st | subst = s })


substitute : Dict Int Type -> Type -> Type
substitute m t =
    case t of
        TVar x ->
            Dict.get x m |> Maybe.withDefault t

        TCon n args ->
            TCon n (List.map (substitute m) args)

        TFun a b ->
            TFun (substitute m a) (substitute m b)

        TTuple ts ->
            TTuple (List.map (substitute m) ts)

        TRecord fields row ->
            let
                fs =
                    Dict.map (\_ x -> substitute m x) fields
            in
            case row |> Maybe.andThen (\r -> Dict.get r m) of
                Just (TVar r2) ->
                    TRecord fs (Just r2)

                Just (TRecord more row2) ->
                    TRecord (Dict.union fs more) row2

                _ ->
                    TRecord fs row


instantiate : Scheme -> St -> ( Type, Dict Int Type, St )
instantiate scheme st0 =
    let
        ( mapping, st1 ) =
            List.foldl
                (\( q, cls ) ( m, st ) ->
                    let
                        ( t, st2 ) =
                            fresh cls st
                    in
                    ( Dict.insert q t m, st2 )
                )
                ( Dict.empty, st0 )
                scheme.quantified
    in
    ( substitute mapping (Types.apply st1.subst scheme.t), mapping, st1 )


fn : List Type -> Type -> Type
fn args result =
    List.foldr TFun result args



-- FREE VARIABLES AND COMPONENTS


freeLocals : Expr -> Set Int
freeLocals e =
    case e of
        EVar _ (Local id _) ->
            Set.singleton id

        EUpdate _ (Local id _) fields ->
            List.foldl (\( _, x ) acc -> Set.union acc (freeLocals x)) (Set.singleton id) fields

        EUpdate _ _ fields ->
            List.foldl (\( _, x ) acc -> Set.union acc (freeLocals x)) Set.empty fields

        EApp f args ->
            List.foldl (\x acc -> Set.union acc (freeLocals x)) (freeLocals f) args

        EBinop _ _ a b ->
            Set.union (freeLocals a) (freeLocals b)

        EIf arms final ->
            List.foldl (\( c, t ) acc -> Set.union acc (Set.union (freeLocals c) (freeLocals t))) (freeLocals final) arms

        ENeg x ->
            freeLocals x

        ETuple xs ->
            List.foldl (\x acc -> Set.union acc (freeLocals x)) Set.empty xs

        EParen x ->
            freeLocals x

        ELet decls body ->
            List.foldl (\d acc -> Set.union acc (declFree d)) (freeLocals body) decls

        ECase s rules ->
            List.foldl (\( _, x ) acc -> Set.union acc (freeLocals x)) (freeLocals s) rules

        ELam _ body ->
            freeLocals body

        ERecord fields ->
            List.foldl (\( _, x ) acc -> Set.union acc (freeLocals x)) Set.empty fields

        EList xs ->
            List.foldl (\x acc -> Set.union acc (freeLocals x)) Set.empty xs

        EAccess x _ ->
            freeLocals x

        _ ->
            Set.empty


declFree : Decl -> Set Int
declFree d =
    case d of
        DFn f ->
            freeLocals f.body

        DPat _ x ->
            freeLocals x


{-| The components of a list of declarations, each as its indices in increasing order, in an order
in which a component comes after the components it refers to; among those ready, the one with the
least member first. The same algorithm as `components` in `Derived.lean`.
-}
components : List Decl -> List (List Int)
components decls =
    let
        arr =
            List.indexedMap Tuple.pair decls

        n =
            List.length decls

        binders i =
            arr |> List.filter (\( j, _ ) -> j == i) |> List.concatMap (Tuple.second >> declBinders >> List.map Tuple.second) |> Set.fromList

        free i =
            arr |> List.filter (\( j, _ ) -> j == i) |> List.map (Tuple.second >> declFree) |> List.foldl Set.union Set.empty

        refers i j =
            not (Set.isEmpty (Set.intersect (free i) (binders j)))

        idx =
            List.range 0 (n - 1)

        reachFrom i =
            let
                go seen todo =
                    case todo of
                        [] ->
                            seen

                        x :: rest ->
                            let
                                next =
                                    List.filter (\j -> refers x j && not (Set.member j seen)) idx
                            in
                            go (Set.union seen (Set.fromList next)) (rest ++ next)
            in
            go (Set.singleton i) [ i ]

        reach =
            Dict.fromList (List.map (\i -> ( i, reachFrom i )) idx)

        r a b =
            Dict.get a reach |> Maybe.map (Set.member b) |> Maybe.withDefault False

        comps =
            List.foldl
                (\a acc ->
                    if List.any (List.member a) acc then
                        acc

                    else
                        acc ++ [ List.filter (\b -> r a b && r b a) idx ]
                )
                []
                idx

        place placed todo =
            case
                List.filter
                    (\cmp ->
                        List.all
                            (\a -> List.all (\b -> not (refers a b) || List.member b cmp || List.any (List.member b) placed) idx)
                            cmp
                    )
                    todo
            of
                cmp :: _ ->
                    place (placed ++ [ cmp ]) (List.filter ((/=) cmp) todo)

                [] ->
                    placed ++ todo
    in
    place [] comps



-- ANNOTATIONS


builtin : String -> Int -> Bool
builtin name arity =
    (List.member name [ "Int", "Float", "Bool", "Char", "String", "Order", "Never" ] && arity == 0)
        || (List.member name [ "List", "Maybe" ] && arity == 1)


classOfName : String -> Class
classOfName name =
    if String.startsWith "number" name then
        Number

    else if String.startsWith "comparable" name then
        Comparable

    else if String.startsWith "compappend" name then
        CompAppend

    else if String.startsWith "appendable" name then
        Appendable

    else
        Any


annotation : Env -> Dict String Type -> Node T.TypeAnnotation -> St -> Result String ( Type, Dict String Type, St )
annotation env scope (Node _ ann) st =
    case ann of
        T.GenericType name ->
            case Dict.get name scope of
                Just t ->
                    Ok ( t, scope, st )

                Nothing ->
                    let
                        ( t, st1 ) =
                            fresh (classOfName name) st
                    in
                    Ok ( t, Dict.insert name t scope, st1 )

        T.Typed (Node _ ( qual, name )) args ->
            annotations env scope args st
                |> Result.andThen
                    (\( targs, scope1, st1 ) ->
                        if (List.isEmpty qual || List.member (String.join "." qual) [ "Basics", "List", "Maybe", "String", "Char" ]) && builtin name (List.length targs) then
                            Ok ( TCon name targs, scope1, st1 )

                        else if not (List.isEmpty qual) then
                            Err ("unknown-type:" ++ String.join "." qual ++ "." ++ name)

                        else
                            case Dict.get name env.program.aliases of
                                Just alias ->
                                    let
                                        aliasScope =
                                            Dict.fromList (List.map2 Tuple.pair alias.params targs)
                                    in
                                    annotation env aliasScope alias.annotation st1
                                        |> Result.map (\( t, _, st2 ) -> ( t, scope1, st2 ))

                                Nothing ->
                                    if Dict.member name env.program.types then
                                        Ok ( TCon name targs, scope1, st1 )

                                    else
                                        Err ("unknown-type:" ++ name)
                    )

        T.Unit ->
            Ok ( TTuple [], scope, st )

        T.Tupled ts ->
            annotations env scope ts st |> Result.map (\( xs, s1, st1 ) -> ( TTuple xs, s1, st1 ))

        T.Record fields ->
            recordFields env scope fields st |> Result.map (\( fs, s1, st1 ) -> ( TRecord fs Nothing, s1, st1 ))

        T.GenericRecord (Node _ rowName) (Node _ fields) ->
            let
                ( rowType, scope1, st1 ) =
                    case Dict.get rowName scope of
                        Just t ->
                            ( t, scope, st )

                        Nothing ->
                            let
                                ( t, s ) =
                                    fresh Any st
                            in
                            ( t, Dict.insert rowName t scope, s )
            in
            recordFields env scope1 fields st1
                |> Result.map
                    (\( fs, s2, st2 ) ->
                        case rowType of
                            TVar r ->
                                ( TRecord fs (Just r), s2, st2 )

                            _ ->
                                ( TRecord fs Nothing, s2, st2 )
                    )

        T.FunctionTypeAnnotation a b ->
            annotation env scope a st
                |> Result.andThen
                    (\( ta, s1, st1 ) ->
                        annotation env s1 b st1 |> Result.map (\( tb, s2, st2 ) -> ( TFun ta tb, s2, st2 ))
                    )


annotations : Env -> Dict String Type -> List (Node T.TypeAnnotation) -> St -> Result String ( List Type, Dict String Type, St )
annotations env scope anns st =
    List.foldl
        (\a acc ->
            acc
                |> Result.andThen
                    (\( ts, s, st1 ) -> annotation env s a st1 |> Result.map (\( t, s2, st2 ) -> ( ts ++ [ t ], s2, st2 )))
        )
        (Ok ( [], scope, st ))
        anns


recordFields : Env -> Dict String Type -> T.RecordDefinition -> St -> Result String ( Dict String Type, Dict String Type, St )
recordFields env scope fields st =
    List.foldl
        (\(Node _ ( Node _ name, t )) acc ->
            acc
                |> Result.andThen
                    (\( fs, s, st1 ) -> annotation env s t st1 |> Result.map (\( tt, s2, st2 ) -> ( Dict.insert name tt fs, s2, st2 )))
        )
        (Ok ( Dict.empty, scope, st ))
        fields


constructorSchemes : Env -> St -> Result String ( Dict String Scheme, St )
constructorSchemes env st0 =
    Dict.foldl
        (\typeName decl acc ->
            acc
                |> Result.andThen
                    (\( d, st ) ->
                        let
                            ( params, st1 ) =
                                List.foldl
                                    (\p ( ps, s ) ->
                                        let
                                            ( t, s1 ) =
                                                fresh Any s
                                        in
                                        ( ps ++ [ ( p, t ) ], s1 )
                                    )
                                    ( [], st )
                                    decl.params

                            scope =
                                Dict.fromList params

                            result =
                                TCon typeName (List.map Tuple.second params)

                            quantified =
                                List.filterMap
                                    (\( _, t ) ->
                                        case t of
                                            TVar x ->
                                                Just ( x, Any )

                                            _ ->
                                                Nothing
                                    )
                                    params
                        in
                        List.foldl
                            (\( k, args ) acc2 ->
                                acc2
                                    |> Result.andThen
                                        (\( d2, s2 ) ->
                                            annotations env scope args s2
                                                |> Result.map (\( targs, _, s3 ) -> ( Dict.insert k { quantified = quantified, t = fn targs result } d2, s3 ))
                                        )
                            )
                            (Ok ( d, st1 ))
                            decl.constructors
                    )
        )
        (Ok ( Dict.empty, st0 ))
        env.program.types



-- EXPRESSIONS


nameScheme : Env -> Name -> Result String Scheme
nameScheme env name =
    case name of
        Local id x ->
            Dict.get id env.values |> Result.fromMaybe ("unbound " ++ x)

        Global m x ->
            if String.left 1 x == String.toUpper (String.left 1 x) then
                Basis.constructor x |> Result.fromMaybe ("unknown constructor " ++ x)

            else
                Basis.value m x |> Result.fromMaybe ("unknown value " ++ m ++ "." ++ x)

        UserCon k ->
            Dict.get k env.cons |> Result.fromMaybe ("unknown constructor " ++ k)


occurrence : Env -> Int -> Name -> St -> R Type
occurrence env occ name st =
    nameScheme env name
        |> Result.map
            (\scheme ->
                let
                    ( t, mapping, st1 ) =
                        instantiate scheme st
                in
                case name of
                    Local id _ ->
                        ( t, { st1 | occurrences = Dict.insert occ { binder = id, instance = mapping } st1.occurrences } )

                    _ ->
                        -- a value of E0: its instance, for the copies of the basis's Elm texts (abs)
                        ( t, { st1 | occurrences = Dict.insert occ { binder = 0, instance = mapping } st1.occurrences } )
            )


operatorType : Int -> String -> St -> R Type
operatorType occ op st =
    case Basis.operator op of
        Just scheme ->
            let
                ( t, mapping, st1 ) =
                    instantiate scheme st
            in
            Ok ( t, { st1 | occurrences = Dict.insert occ { binder = 0, instance = mapping } st1.occurrences } )

        Nothing ->
            Err ("unknown operator " ++ op)


expr : Env -> Expr -> St -> R Type
expr env e st =
    case e of
        EUnit ->
            Ok ( TTuple [], st )

        EApp f args ->
            expr env f st
                |> Result.andThen
                    (\( tf, st1 ) ->
                        List.foldl
                            (\a acc ->
                                acc
                                    |> Result.andThen
                                        (\( tfun, s ) ->
                                            expr env a s
                                                |> Result.andThen
                                                    (\( ta, s1 ) ->
                                                        let
                                                            ( r, s2 ) =
                                                                fresh Any s1
                                                        in
                                                        unify tfun (TFun ta r) s2 |> Result.map (\s3 -> ( r, s3 ))
                                                    )
                                        )
                            )
                            (Ok ( tf, st1 ))
                            args
                    )

        EBinop occ op l r ->
            operatorType occ op st
                |> Result.andThen
                    (\( top, st1 ) ->
                        expr env l st1
                            |> Result.andThen
                                (\( tl, st2 ) ->
                                    expr env r st2
                                        |> Result.andThen
                                            (\( tr, st3 ) ->
                                                let
                                                    ( res, st4 ) =
                                                        fresh Any st3
                                                in
                                                unify top (fn [ tl, tr ] res) st4 |> Result.map (\s -> ( res, s ))
                                            )
                                )
                    )

        EVar occ name ->
            occurrence env occ name st

        ECon name ->
            nameScheme env name
                |> Result.map
                    (\scheme ->
                        let
                            ( t, _, st1 ) =
                                instantiate scheme st
                        in
                        ( t, st1 )
                    )

        EIf arms final ->
            expr env final st
                |> Result.andThen
                    (\( tfinal, st1 ) ->
                        List.foldl
                            (\( c, t ) acc ->
                                acc
                                    |> Result.andThen
                                        (\s ->
                                            expr env c s
                                                |> Result.andThen (\( tc, s1 ) -> unify tc (TCon "Bool" []) s1)
                                                |> Result.andThen (\s2 -> expr env t s2)
                                                |> Result.andThen (\( tt, s3 ) -> unify tt tfinal s3)
                                        )
                            )
                            (Ok st1)
                            arms
                            |> Result.map (\s -> ( tfinal, s ))
                    )

        EOp occ op ->
            operatorType occ op st

        EInt id _ ->
            let
                ( t, st1 ) =
                    fresh Number st
            in
            Ok ( t, { st1 | literals = Dict.insert id t st1.literals } )

        EIntAt isFloat _ ->
            Ok
                ( if isFloat then
                    TCon "Float" []

                  else
                    TCon "Int" []
                , st
                )

        EFloat _ ->
            Ok ( TCon "Float" [], st )

        ENeg x ->
            expr env x st
                |> Result.andThen
                    (\( tx, st1 ) ->
                        let
                            ( n, st2 ) =
                                fresh Number st1
                        in
                        unify tx n st2 |> Result.map (\s -> ( n, s ))
                    )

        EStr _ ->
            Ok ( TCon "String" [], st )

        EChar _ ->
            Ok ( TCon "Char" [], st )

        ETuple xs ->
            exprList env xs st |> Result.map (\( ts, s ) -> ( TTuple ts, s ))

        EParen x ->
            expr env x st

        ELet decls body ->
            declarations env decls st |> Result.andThen (\( env1, st1 ) -> expr env1 body st1)

        ECase scrutinee rules ->
            expr env scrutinee st
                |> Result.andThen
                    (\( ts, st1 ) ->
                        let
                            ( result, st2 ) =
                                fresh Any st1
                        in
                        List.foldl
                            (\( p, b ) acc ->
                                acc
                                    |> Result.andThen
                                        (\s ->
                                            pattern env p s
                                                |> Result.andThen
                                                    (\( ( tp, bound ), s1 ) ->
                                                        unify ts tp s1
                                                            |> Result.andThen (\s2 -> expr (bindMono bound env) b s2)
                                                            |> Result.andThen (\( tb, s3 ) -> unify tb result s3)
                                                    )
                                        )
                            )
                            (Ok st2)
                            rules
                            |> Result.map (\s -> ( result, s ))
                    )

        ELam ps body ->
            patternList env ps st
                |> Result.andThen
                    (\( ( tps, bound ), st1 ) ->
                        expr (bindMono bound env) body st1 |> Result.map (\( tb, s ) -> ( fn tps tb, s ))
                    )

        ERecord fields ->
            List.foldl
                (\( f, x ) acc ->
                    acc |> Result.andThen (\( d, s ) -> expr env x s |> Result.map (\( tx, s1 ) -> ( Dict.insert f tx d, s1 )))
                )
                (Ok ( Dict.empty, st ))
                fields
                |> Result.map (\( d, s ) -> ( TRecord d Nothing, s ))

        EList xs ->
            let
                ( elem, st1 ) =
                    fresh Any st
            in
            List.foldl
                (\x acc -> acc |> Result.andThen (\s -> expr env x s |> Result.andThen (\( tx, s1 ) -> unify tx elem s1)))
                (Ok st1)
                xs
                |> Result.map (\s -> ( TCon "List" [ elem ], s ))

        EAccess x f ->
            expr env x st
                |> Result.andThen
                    (\( tx, st1 ) ->
                        let
                            ( tf, st2 ) =
                                fresh Any st1

                            ( row, st3 ) =
                                fresh Any st2
                        in
                        case row of
                            TVar r ->
                                unify tx (TRecord (Dict.singleton f tf) (Just r)) st3 |> Result.map (\s -> ( tf, s ))

                            _ ->
                                Err "row"
                    )

        EAccessor f ->
            let
                ( tf, st1 ) =
                    fresh Any st

                ( row, st2 ) =
                    fresh Any st1
            in
            case row of
                TVar r ->
                    Ok ( TFun (TRecord (Dict.singleton f tf) (Just r)) tf, st2 )

                _ ->
                    Err "row"

        EUpdate occ name fields ->
            occurrence env occ name st
                |> Result.andThen
                    (\( tr, st1 ) ->
                        List.foldl
                            (\( f, x ) acc ->
                                acc |> Result.andThen (\( d, s ) -> expr env x s |> Result.map (\( tx, s1 ) -> ( Dict.insert f tx d, s1 )))
                            )
                            (Ok ( Dict.empty, st1 ))
                            fields
                            |> Result.andThen
                                (\( d, st2 ) ->
                                    let
                                        ( row, st3 ) =
                                            fresh Any st2
                                    in
                                    case row of
                                        TVar r ->
                                            unify tr (TRecord d (Just r)) st3 |> Result.map (\s -> ( tr, s ))

                                        _ ->
                                            Err "row"
                                )
                    )


exprList : Env -> List Expr -> St -> R (List Type)
exprList env xs st =
    List.foldl
        (\x acc -> acc |> Result.andThen (\( ts, s ) -> expr env x s |> Result.map (\( t, s1 ) -> ( ts ++ [ t ], s1 ))))
        (Ok ( [], st ))
        xs


bindMono : List ( Int, Type ) -> Env -> Env
bindMono bound env =
    { env | values = List.foldl (\( id, t ) d -> Dict.insert id { quantified = [], t = t } d) env.values bound }



-- PATTERNS


pattern : Env -> Pattern -> St -> R ( Type, List ( Int, Type ) )
pattern env p st =
    case p of
        PWild ->
            let
                ( t, st1 ) =
                    fresh Any st
            in
            Ok ( ( t, [] ), st1 )

        PUnit ->
            Ok ( ( TTuple [], [] ), st )

        PChar _ ->
            Ok ( ( TCon "Char" [], [] ), st )

        PStr _ ->
            Ok ( ( TCon "String" [], [] ), st )

        PInt _ ->
            Ok ( ( TCon "Int" [], [] ), st )

        PTuple ps ->
            patternList env ps st |> Result.map (\( ( ts, bound ), s ) -> ( ( TTuple ts, bound ), s ))

        PRecord fields ->
            let
                ( typed, st1 ) =
                    List.foldl
                        (\( f, id ) ( acc, s ) ->
                            let
                                ( t, s1 ) =
                                    fresh Any s
                            in
                            ( acc ++ [ ( f, id, t ) ], s1 )
                        )
                        ( [], st )
                        fields

                ( row, st2 ) =
                    fresh Any st1
            in
            case row of
                TVar r ->
                    Ok
                        ( ( TRecord (Dict.fromList (List.map (\( f, _, t ) -> ( f, t )) typed)) (Just r)
                          , List.map (\( _, id, t ) -> ( id, t )) typed
                          )
                        , st2
                        )

                _ ->
                    Err "row"

        PCons a b ->
            pattern env a st
                |> Result.andThen
                    (\( ( ta, ba ), st1 ) ->
                        pattern env b st1
                            |> Result.andThen
                                (\( ( tb, bb ), st2 ) ->
                                    unify tb (TCon "List" [ ta ]) st2 |> Result.map (\s -> ( ( tb, ba ++ bb ), s ))
                                )
                    )

        PList ps ->
            let
                ( elem, st1 ) =
                    fresh Any st
            in
            List.foldl
                (\q acc ->
                    acc
                        |> Result.andThen
                            (\( bound, s ) ->
                                pattern env q s
                                    |> Result.andThen (\( ( tq, bq ), s1 ) -> unify tq elem s1 |> Result.map (\s2 -> ( bound ++ bq, s2 )))
                            )
                )
                (Ok ( [], st1 ))
                ps
                |> Result.map (\( bound, s ) -> ( ( TCon "List" [ elem ], bound ), s ))

        PVar _ id ->
            let
                ( t, st1 ) =
                    fresh Any st
            in
            Ok ( ( t, [ ( id, t ) ] ), st1 )

        PCon name args ->
            nameScheme env name
                |> Result.andThen
                    (\scheme ->
                        let
                            ( tcon, _, st1 ) =
                                instantiate scheme st
                        in
                        patternList env args st1
                            |> Result.andThen
                                (\( ( targs, bound ), st2 ) ->
                                    let
                                        ( result, st3 ) =
                                            fresh Any st2
                                    in
                                    unify tcon (fn targs result) st3 |> Result.map (\s -> ( ( result, bound ), s ))
                                )
                    )

        PAs q _ id ->
            pattern env q st |> Result.map (\( ( t, bound ), s ) -> ( ( t, bound ++ [ ( id, t ) ] ), s ))

        PParen q ->
            pattern env q st


patternList : Env -> List Pattern -> St -> R ( List Type, List ( Int, Type ) )
patternList env ps st =
    List.foldl
        (\p acc ->
            acc
                |> Result.andThen
                    (\( ( ts, bound ), s ) ->
                        pattern env p s |> Result.map (\( ( t, b ), s1 ) -> ( ( ts ++ [ t ], bound ++ b ), s1 ))
                    )
        )
        (Ok ( ( [], [] ), st ))
        ps



-- DECLARATIONS


envFree : Env -> St -> Set Int
envFree env st =
    Dict.foldl
        (\_ scheme acc ->
            Set.union acc
                (Set.diff (Types.ftv st.subst scheme.t) (Set.fromList (List.map Tuple.first scheme.quantified)))
        )
        Set.empty
        env.values


declarations : Env -> List Decl -> St -> R Env
declarations env decls st =
    let
        indexed =
            List.indexedMap Tuple.pair decls
    in
    List.foldl
        (\cmp acc ->
            acc
                |> Result.andThen
                    (\( e, s ) ->
                        component e (List.filterMap (\i -> List.filter (\( j, _ ) -> j == i) indexed |> List.head |> Maybe.map Tuple.second) cmp) s
                    )
        )
        (Ok ( env, st ))
        (components decls)


component : Env -> List Decl -> St -> R Env
component env decls st0 =
    let
        -- each binder's provisional scheme: an annotation's, generalised over its own variables, or a monotype
        provisional =
            List.foldl
                (\d acc ->
                    acc
                        |> Result.andThen
                            (\( entries, st ) ->
                                case d of
                                    DFn f ->
                                        case f.annotation of
                                            Just ann ->
                                                annotation env env.annVars ann st
                                                    |> Result.map
                                                        (\( t, scope, st1 ) ->
                                                            let
                                                                own =
                                                                    Dict.diff scope env.annVars |> Dict.values |> List.filterMap varOf
                                                            in
                                                            ( entries ++ [ ( f.binder, { quantified = List.map (\v -> ( v, Types.classOf st1.subst v )) own, t = t }, scope ) ], st1 )
                                                        )

                                            Nothing ->
                                                let
                                                    ( t, st1 ) =
                                                        fresh Any st
                                                in
                                                Ok ( entries ++ [ ( f.binder, { quantified = [], t = t }, env.annVars ) ], st1 )

                                    DPat p _ ->
                                        Ok ( entries, st )
                            )
                )
                (Ok ( [], st0 ))
                decls
    in
    provisional
        |> Result.andThen
            (\( entries, st1 ) ->
                let
                    envIn =
                        { env | values = List.foldl (\( id, scheme, _ ) d -> Dict.insert id scheme d) env.values entries }

                    scopeOf id =
                        entries |> List.filter (\( b, _, _ ) -> b == id) |> List.head |> Maybe.map (\( _, _, s ) -> s) |> Maybe.withDefault env.annVars

                    schemeOf id =
                        entries |> List.filter (\( b, _, _ ) -> b == id) |> List.head |> Maybe.map (\( _, s, _ ) -> s)
                in
                List.foldl
                    (\d acc ->
                        acc
                            |> Result.andThen
                                (\( bound, st ) ->
                                    case d of
                                        DFn f ->
                                            patternList envIn f.args st
                                                |> Result.andThen
                                                    (\( ( targs, argBound ), stA ) ->
                                                        expr (bindMono argBound { envIn | annVars = scopeOf f.binder }) f.body stA
                                                            |> Result.andThen
                                                                (\( tbody, stB ) ->
                                                                    case schemeOf f.binder of
                                                                        Just scheme ->
                                                                            unify (fn targs tbody) scheme.t stB
                                                                                |> Result.map (\stC -> ( bound ++ [ ( f.binder, scheme.t ) ], stC ))

                                                                        Nothing ->
                                                                            Err "binder"
                                                                )
                                                    )

                                        DPat p x ->
                                            pattern envIn p st
                                                |> Result.andThen
                                                    (\( ( tp, pBound ), stA ) ->
                                                        expr envIn x stA
                                                            |> Result.andThen (\( tx, stB ) -> unify tp tx stB)
                                                            |> Result.map (\stC -> ( bound ++ pBound, stC ))
                                                    )
                                )
                    )
                    (Ok ( [], st1 ))
                    decls
                    |> Result.map (\( bound, st2 ) -> generalise env bound st2)
            )


varOf : Type -> Maybe Int
varOf t =
    case t of
        TVar v ->
            Just v

        _ ->
            Nothing


{-| Closes the component's bindings, every one over all the component's `number` variables (A93),
and records the group of each binder.
-}
generalise : Env -> List ( Int, Type ) -> St -> ( Env, St )
generalise env bound st =
    let
        outer =
            envFree env st

        frees =
            List.map (\( id, t ) -> ( id, Set.diff (Types.ftv st.subst t) outer )) bound

        groupNumbers =
            frees
                |> List.foldl (\( _, vs ) acc -> Set.union acc vs) Set.empty
                |> Set.filter (\v -> Types.classOf st.subst v == Number)
                |> Set.toList

        key =
            bound |> List.map Tuple.first |> List.minimum |> Maybe.withDefault -1

        schemes =
            List.map
                (\( id, vs ) ->
                    ( id
                    , { quantified =
                            Set.union vs (Set.fromList groupNumbers)
                                |> Set.toList
                                |> List.map (\v -> ( v, Types.classOf st.subst v ))
                      , t =
                            bound
                                |> List.filter (\( b, _ ) -> b == id)
                                |> List.head
                                |> Maybe.map (Tuple.second >> Types.apply st.subst)
                                |> Maybe.withDefault (TTuple [])
                      }
                    )
                )
                frees
    in
    ( { env | values = List.foldl (\( id, s ) d -> Dict.insert id s d) env.values schemes }
    , { st
        | groupKey = List.foldl (\( id, _ ) d -> Dict.insert id key d) st.groupKey bound
        , groupVars = Dict.insert key groupNumbers st.groupVars
      }
    )



-- THE PROGRAM


infer : TestProgram -> Result String Inferred
infer program =
    let
        st0 =
            { subst = Types.emptySubst
            , literals = Dict.empty
            , occurrences = Dict.empty
            , groupKey = Dict.empty
            , groupVars = Dict.empty
            }

        env0 =
            { values = Dict.empty, annVars = Dict.empty, program = program, cons = Dict.empty }
    in
    constructorSchemes env0 st0
        |> Result.andThen
            (\( cons, st1 ) ->
                let
                    env1 =
                        { env0 | cons = cons }
                in
                declarations env1 program.defs st1
                    |> Result.andThen (\( env2, st2 ) -> declarations env2 program.locals st2)
                    |> Result.andThen
                        (\( env3, st3 ) ->
                            List.foldl
                                (\c acc -> acc |> Result.andThen (\( ts, s ) -> expr env3 c.expr s |> Result.map (\( t, s1 ) -> ( ts ++ [ t ], s1 ))))
                                (Ok ( [], st3 ))
                                program.checks
                        )
                    |> Result.map
                        (\( checkTypes, st4 ) ->
                            { subst = st4.subst
                            , literals = st4.literals
                            , occurrences = st4.occurrences
                            , groupKey = st4.groupKey
                            , groupVars = st4.groupVars
                            , checkTypes = checkTypes
                            }
                        )
            )
