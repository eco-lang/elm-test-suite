module Translate.Types exposing
    ( Class(..)
    , Scheme
    , Subst
    , Type(..)
    , apply
    , classOf
    , emptySubst
    , freshVar
    , ftv
    , merge
    , show
    , tyVarsSeq
    , unify
    , walk
    )

{-| Types, type schemes and unification for the translator's inference (B.7): Hindley-Milner types
with the classes of Standard Elm and rows for records.
-}

import Dict exposing (Dict)
import Set exposing (Set)


type Type
    = TVar Int
    | TCon String (List Type)
    | TFun Type Type
    | TTuple (List Type)
    | TRecord (Dict String Type) (Maybe Int)


type Class
    = Any
    | Number
    | Comparable
    | Appendable
    | CompAppend


{-| A type scheme: the quantified variables with their classes, and the type.
-}
type alias Scheme =
    { quantified : List ( Int, Class ), t : Type }


type alias Subst =
    { bound : Dict Int Type
    , classes : Dict Int Class
    , next : Int
    }


emptySubst : Subst
emptySubst =
    { bound = Dict.empty, classes = Dict.empty, next = 1 }


freshVar : Class -> Subst -> ( Type, Subst )
freshVar cls s =
    ( TVar s.next, { s | next = s.next + 1, classes = Dict.insert s.next cls s.classes } )


classOf : Subst -> Int -> Class
classOf s v =
    Dict.get v s.classes |> Maybe.withDefault Any


{-| The more specific of two classes.
-}
merge : Class -> Class -> Class
merge a b =
    case ( a, b ) of
        ( Number, _ ) ->
            Number

        ( _, Number ) ->
            Number

        ( Any, x ) ->
            x

        ( x, Any ) ->
            x

        ( Comparable, Appendable ) ->
            CompAppend

        ( Appendable, Comparable ) ->
            CompAppend

        ( CompAppend, _ ) ->
            CompAppend

        ( _, CompAppend ) ->
            CompAppend

        ( x, _ ) ->
            x


{-| A type with its head variable followed through the substitution.
-}
walk : Subst -> Type -> Type
walk s t =
    case t of
        TVar v ->
            case Dict.get v s.bound of
                Just u ->
                    walk s u

                Nothing ->
                    t

        _ ->
            t


{-| A type with the substitution applied everywhere; a record whose row variable is bound is
flattened.
-}
apply : Subst -> Type -> Type
apply s t =
    case walk s t of
        TVar v ->
            TVar v

        TCon n args ->
            TCon n (List.map (apply s) args)

        TFun a b ->
            TFun (apply s a) (apply s b)

        TTuple ts ->
            TTuple (List.map (apply s) ts)

        TRecord fields row ->
            let
                fs =
                    Dict.map (\_ v -> apply s v) fields
            in
            case row of
                Nothing ->
                    TRecord fs Nothing

                Just r ->
                    case apply s (TVar r) of
                        TRecord more row2 ->
                            TRecord (Dict.union fs more) row2

                        TVar r2 ->
                            TRecord fs (Just r2)

                        _ ->
                            TRecord fs (Just r)


ftv : Subst -> Type -> Set Int
ftv s t =
    case apply s t of
        TVar v ->
            Set.singleton v

        TCon _ args ->
            List.foldl (\a acc -> Set.union acc (ftv s a)) Set.empty args

        TFun a b ->
            Set.union (ftv s a) (ftv s b)

        TTuple ts ->
            List.foldl (\a acc -> Set.union acc (ftv s a)) Set.empty ts

        TRecord fields row ->
            Dict.foldl (\_ a acc -> Set.union acc (ftv s a)) (row |> Maybe.map Set.singleton |> Maybe.withDefault Set.empty) fields


{-| The type variables of a type in order of first occurrence, duplicates kept (step 10, Choices,
item 2; Lean's `Ty.tyVarsSeq`): the arguments of a constructed type and the components of a tuple
in order, the domain before the range, the fields of a record in label order (`Dict`'s order). The
row variable of an open record is not a type variable and is not listed.
-}
tyVarsSeq : Subst -> Type -> List Int
tyVarsSeq s t =
    case apply s t of
        TVar v ->
            [ v ]

        TCon _ args ->
            List.concatMap (tyVarsSeq s) args

        TFun a b ->
            tyVarsSeq s a ++ tyVarsSeq s b

        TTuple ts ->
            List.concatMap (tyVarsSeq s) ts

        TRecord fields _ ->
            Dict.values fields |> List.concatMap (tyVarsSeq s)


occurs : Subst -> Int -> Type -> Bool
occurs s v t =
    Set.member v (ftv s t)


bindVar : Int -> Type -> Subst -> Result String Subst
bindVar v t s =
    case walk s t of
        TVar u ->
            if u == v then
                Ok s

            else
                Ok
                    { s
                        | bound = Dict.insert v (TVar u) s.bound
                        , classes = Dict.insert u (merge (classOf s v) (classOf s u)) s.classes
                    }

        other ->
            if occurs s v other then
                Err ("infinite type: " ++ show s (TVar v) ++ " in " ++ show s other)

            else
                case ( classOf s v, other ) of
                    ( Number, TCon "Int" [] ) ->
                        Ok { s | bound = Dict.insert v other s.bound }

                    ( Number, TCon "Float" [] ) ->
                        Ok { s | bound = Dict.insert v other s.bound }

                    ( Number, _ ) ->
                        Err ("not a number: " ++ show s other)

                    _ ->
                        Ok { s | bound = Dict.insert v other s.bound }


unify : Type -> Type -> Subst -> Result String Subst
unify a b s =
    case ( walk s a, walk s b ) of
        ( TVar v, t ) ->
            bindVar v t s

        ( t, TVar v ) ->
            bindVar v t s

        ( TCon n as_, TCon m bs ) ->
            if n == m && List.length as_ == List.length bs then
                unifyAll as_ bs s

            else
                Err (show s a ++ " is not " ++ show s b)

        ( TFun a1 b1, TFun a2 b2 ) ->
            unify a1 a2 s |> Result.andThen (unify b1 b2)

        ( TTuple xs, TTuple ys ) ->
            if List.length xs == List.length ys then
                unifyAll xs ys s

            else
                Err (show s a ++ " is not " ++ show s b)

        ( TRecord _ _, TRecord _ _ ) ->
            unifyRecords (apply s a) (apply s b) s

        _ ->
            Err (show s a ++ " is not " ++ show s b)


unifyAll : List Type -> List Type -> Subst -> Result String Subst
unifyAll xs ys s =
    List.map2 Tuple.pair xs ys
        |> List.foldl (\( x, y ) acc -> Result.andThen (unify x y) acc) (Ok s)


unifyRecords : Type -> Type -> Subst -> Result String Subst
unifyRecords a b s =
    case ( a, b ) of
        ( TRecord fa ra, TRecord fb rb ) ->
            let
                common =
                    Dict.keys (Dict.intersect fa fb)

                onlyA =
                    Dict.diff fa fb

                onlyB =
                    Dict.diff fb fa

                s1 =
                    List.foldl
                        (\k acc ->
                            Result.andThen
                                (unify (Dict.get k fa |> Maybe.withDefault (TTuple [])) (Dict.get k fb |> Maybe.withDefault (TTuple [])))
                                acc
                        )
                        (Ok s)
                        common
            in
            s1
                |> Result.andThen
                    (\s2 ->
                        case ( ra, rb ) of
                            ( Nothing, Nothing ) ->
                                if Dict.isEmpty onlyA && Dict.isEmpty onlyB then
                                    Ok s2

                                else
                                    Err ("records with different fields: " ++ show s2 a ++ " and " ++ show s2 b)

                            ( Just r, Nothing ) ->
                                if Dict.isEmpty onlyA then
                                    bindVar r (TRecord onlyB Nothing) s2

                                else
                                    Err ("a closed record lacks fields: " ++ show s2 b)

                            ( Nothing, Just r ) ->
                                if Dict.isEmpty onlyB then
                                    bindVar r (TRecord onlyA Nothing) s2

                                else
                                    Err ("a closed record lacks fields: " ++ show s2 a)

                            ( Just r1, Just r2 ) ->
                                if r1 == r2 then
                                    if Dict.isEmpty onlyA && Dict.isEmpty onlyB then
                                        Ok s2

                                    else
                                        Err "a row cannot have different fields"

                                else
                                    let
                                        ( rho, s3 ) =
                                            freshVar Any s2
                                    in
                                    case rho of
                                        TVar rv ->
                                            bindVar r1 (TRecord onlyB (Just rv)) s3
                                                |> Result.andThen (bindVar r2 (TRecord onlyA (Just rv)))

                                        _ ->
                                            Err "fresh row"
                    )

        _ ->
            Err "records"


show : Subst -> Type -> String
show s t =
    case apply s t of
        TVar v ->
            case classOf s v of
                Number ->
                    "number" ++ String.fromInt v

                Comparable ->
                    "comparable" ++ String.fromInt v

                _ ->
                    "t" ++ String.fromInt v

        TCon n [] ->
            n

        TCon n args ->
            "(" ++ n ++ " " ++ String.join " " (List.map (show s) args) ++ ")"

        TFun x y ->
            "(" ++ show s x ++ " -> " ++ show s y ++ ")"

        TTuple [] ->
            "()"

        TTuple ts ->
            "(" ++ String.join ", " (List.map (show s) ts) ++ ")"

        TRecord fields row ->
            "{ "
                ++ (row |> Maybe.map (\r -> "r" ++ String.fromInt r ++ " | ") |> Maybe.withDefault "")
                ++ String.join ", " (List.map (\( k, v ) -> k ++ " : " ++ show s v) (Dict.toList fields))
                ++ " }"
