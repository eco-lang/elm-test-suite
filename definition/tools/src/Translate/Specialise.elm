module Translate.Specialise exposing (CheckKind(..), Specialised, specialise, specialiseLibrary, specialiseWith)

{-| Number specialisation (A Standard Definition of Elm?, sec:dynamic-core-numbers; rulings A87,
A27, A93; plans/elm-to-lean-translator.md, B.8). Each declaration whose bindings quantify `number`
variables is replaced by its default copy (every such variable Float, under its own names) and one
copy for each other assignment of Int or Float at which the program uses it, under new names; each
occurrence refers to the copy for its instance; a `number` variable nothing fixes is Float. Copies are
made from the outside in: each scope finds the copies its declarations need by a fixpoint over the
copies already made and its body.
-}

import Dict exposing (Dict)
import Set exposing (Set)
import Translate.Basis as Basis
import Translate.Infer as Infer exposing (Inferred)
import Translate.Ir exposing (..)
import Translate.Library as Library exposing (Library)
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

    -- each port's direction (outgoing or not) and payload, by binding id
    , ports : Dict Int ( Bool, Payload )

    -- a worker's flags type as a payload type; Nothing for a view
    , flags : Maybe Payload

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


{-| The type a `number` variable takes when nothing fixes it, and in a default copy: Float (ruling
A27).
-}
defaultNum : Num
defaultNum =
    FloatN


isDefault : Assignment -> Bool
isDefault =
    List.all (\( _, n ) -> n == defaultNum)


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
    , library : Library
    }


{-| A type read as Int or Float under the assignments of the enclosing copies; a `number` variable
they do not fix is Float.
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
                        Ok defaultNum

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
            declared ctx occ name id x (\n -> Local id n)

        Foreign f ->
            -- a value of another module: renamed to its copy as a local one is, its qualifier kept
            declared ctx occ name f.binder f.name (\n -> Foreign { f | name = n })

        Global m x ->
            basisOccurrence ctx occ name m x (Global m)

        Exposed m x ->
            basisOccurrence ctx occ name m x (Exposed m)

        _ ->
            Ok ( name, [] )


{-| The `number` variables of a value of the basis written in Elm whose scheme quantifies them,
in the scheme's order: `abs` (Appendix D) and the core library's (`List.sum`, decision L3). [] for
any other value: it has no copies.
-}
basisCopied : Library -> String -> String -> List Int
basisCopied lib m x =
    if x == "abs" && (m == "" || m == "Basics") then
        Basis.value m x
            |> Maybe.map (.quantified >> List.filter (\( _, c ) -> c == Number) >> List.map Tuple.first)
            |> Maybe.withDefault []

    else
        Library.copied lib m x


{-| An occurrence of a value of the basis: the Elm texts of the basis and of the core library are
specialised too, and a use of one whose scheme quantifies `number` variables at an assignment other
than the default is its copy (`abs` used at Int is `abs$Int`, `List.sum` used at Int is
`List.sum$Int`), written as the source writes the value.
-}
basisOccurrence : Ctx -> Int -> Name -> String -> String -> (String -> Name) -> Result String ( Name, List Request )
basisOccurrence ctx occ name m x rename =
    case basisCopied ctx.library m x of
        [] ->
            Ok ( name, [] )

        vars ->
            case Dict.get occ ctx.inferred.occurrences of
                Just o ->
                    vars
                        |> List.map
                            (\v ->
                                case Dict.get v o.instance of
                                    Just t ->
                                        resolve ctx t |> Result.map (\n -> ( v, n ))

                                    Nothing ->
                                        Ok ( v, defaultNum )
                            )
                        |> combine
                        |> Result.map
                            (\a ->
                                if isDefault a then
                                    ( name, [] )

                                else
                                    ( rename (copyName x a), [] )
                            )

                Nothing ->
                    Ok ( name, [] )


{-| An occurrence of the variable `x` declared by binding `id`: the copy it refers to (`rename`
builds the occurrence's name from the copy's), and the request for that copy.
-}
declared : Ctx -> Int -> Name -> Int -> String -> (String -> Name) -> Result String ( Name, List Request )
declared ctx occ name id x rename =
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
                        Ok (Dict.get g ctx.own |> Maybe.withDefault (List.map (\v -> ( v, defaultNum )) vars))

                    else
                        vars
                            |> List.map
                                (\v ->
                                    case Dict.get v instance of
                                        Just t ->
                                            resolve ctx t |> Result.map (\n -> ( v, n ))

                                        Nothing ->
                                            if Dict.member g ctx.own then
                                                -- inside its group, a variable the scheme seen here
                                                -- does not bind (an annotated member's U' only):
                                                -- the enclosing copy's (step 10, Choices, item 5)
                                                Ok ( v, Dict.get v ctx.rho |> Maybe.withDefault defaultNum )

                                            else
                                                -- outside its group nothing at the occurrence fixes
                                                -- it: Float (sec:dynamic-core-numbers; the Lean
                                                -- side's Member.bOutAll, finding of 2026-11-12)
                                                Ok ( v, defaultNum )
                                )
                            |> combine
            in
            assignment
                |> Result.map (\a -> ( rename (copyName x a), [ { group = g, assignment = a } ] ))


{-| An operator, renamed `^@Float` when it is `^` at Float: the same operator of OT\_dyn, marked
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
                [ "round", "floor", "ceiling", "truncate", "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "logBase", "fromPolar", "toPolar" ]
        )


isNative : Expr -> Bool
isNative e =
    case e of
        EVar _ name ->
            case globalOf name of
                Just mx ->
                    Set.member mx nativeValues

                Nothing ->
                    False

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
                        { cmp = cmp, group = g, gid = Maybe.withDefault -(n + 1) g, default = List.map (\v -> ( v, defaultNum )) vars }
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
                                                            |> List.sortBy
                                                                (\a ->
                                                                    ( if isDefault a then
                                                                        0

                                                                      else
                                                                        1
                                                                    , key a
                                                                    )
                                                                )
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
                KFloat

            else
                KData

        _ ->
            KData


specialise : TestProgram -> Inferred -> Result String Specialised
specialise =
    specialiseWith Library.empty


{-| The specialisation of a program that may name the values of the core library `lib`.
-}
specialiseWith : Library -> TestProgram -> Inferred -> Result String Specialised
specialiseWith lib program inferred =
    let
        ctx =
            { inferred = inferred, rho = Dict.empty, own = Dict.empty, library = lib }

        -- the kind of a line's value: the type at which its label is logged (the `a` of
        -- `Debug.log : String -> a -> a`), when every occurrence of the label agrees
        logged t =
            case Types.apply inferred.subst t of
                TFun _ (TFun a _) ->
                    Just a

                _ ->
                    Nothing

        kindOfLine line =
            case lineLabel line of
                Just label ->
                    case Dict.get label inferred.logTypes |> Maybe.withDefault [] |> List.filterMap logged |> List.map (kindOf ctx) of
                        k :: ks ->
                            if List.all ((==) k) ks then
                                k

                            else
                                KData

                        [] ->
                            KData

                Nothing ->
                    KData
    in
    -- the modules as nested scopes, in program order: a use in a later module of an earlier
    -- module's declaration requests its copy, which is placed in the earlier module
    (case inferred.flagsType of
        Just t ->
            case Infer.payloadOf (Types.apply inferred.subst t) of
                Ok p ->
                    Ok (Just p)

                Err _ ->
                    Err "construct:flags-type"

        Nothing ->
            Ok Nothing
    )
        |> Result.andThen (\flags -> scopes ctx program.modules |> Result.map (\r -> ( r, flags )))
        |> Result.map
            (\( ( defsByModule, _ ), flags ) ->
                let
                    modules =
                        List.map2 (\m defs -> { m | defs = defs }) program.modules defsByModule

                    copiesOf =
                        Dict.fromList (List.map (\m -> ( m.name, List.concatMap declNames m.defs )) modules)

                    -- an exposing item stands for its copies (dynamic-modules.tex, lines 74 to 79)
                    withCopies names x =
                        case x of
                            ExposeAll ->
                                ExposeAll

                            ExposeItems items ->
                                ExposeItems
                                    (List.concatMap
                                        (\item ->
                                            case item of
                                                IVar v ->
                                                    IVar v :: List.map IVar (List.filter (String.startsWith (v ++ "$")) names)

                                                _ ->
                                                    [ item ]
                                        )
                                        items
                                    )

                    exposed =
                        List.map
                            (\m ->
                                { m
                                    | exposes = withCopies (List.concatMap declNames m.defs) m.exposes
                                    , imports =
                                        List.map
                                            (\imp ->
                                                case Dict.get imp.modid copiesOf of
                                                    Just names ->
                                                        { imp | exposes = Maybe.map (withCopies names) imp.exposes }

                                                    Nothing ->
                                                        -- a module of the basis: the copies the
                                                        -- basis binds (`import List exposing (sum)`
                                                        -- exposes `sum$Int` too)
                                                        { imp | exposes = Maybe.map (withCopies (basisCopyNames lib imp.modid imp.exposes)) imp.exposes }
                                            )
                                            m.imports
                                }
                            )
                            modules

                    allDefs =
                        List.concatMap .defs modules
                in
                { program = { program | modules = exposed }
                , kinds = List.map kindOfLine program.checks
                , ports = inferred.ports
                , flags = flags
                , native = List.any (anyExpr isNative) (List.concatMap declExprs allDefs)
                }
            )


{-| The modules' declarations, each module a scope around the modules after it.
-}
scopes : Ctx -> List ModuleIr -> Out (List (List Decl))
scopes ctx modules =
    case modules of
        [] ->
            Ok ( [], [] )

        m :: rest ->
            scope ctx m.defs (\c -> scopes c rest)
                |> Result.map (\( ( defs, inner ), requests ) -> ( defs :: inner, requests ))


declNames : Decl -> List String
declNames d =
    List.map Tuple.first (declBinders d)


declExprs : Decl -> List Expr
declExprs d =
    case d of
        DFn f ->
            [ f.body ]

        DPat _ x ->
            [ x ]


{-| The copies a module of the basis binds of the values an exposing list names: every assignment
of each copied value's `number` variables but the default, in the order of their keys.
-}
basisCopyNames : Library -> String -> Maybe ExposingIr -> List String
basisCopyNames lib modid exposes =
    case exposes of
        Just (ExposeItems items) ->
            items
                |> List.concatMap
                    (\item ->
                        case item of
                            IVar x ->
                                allAssignments (basisCopied lib modid x)
                                    |> List.filter (not << isDefault)
                                    |> List.sortBy key
                                    |> List.map (copyName x)

                            _ ->
                                []
                    )

        _ ->
            []


{-| Every assignment of the variables (2^n of them).
-}
allAssignments : List Int -> List Assignment
allAssignments vars =
    case vars of
        [] ->
            [ [] ]

        v :: rest ->
            allAssignments rest |> List.concatMap (\a -> [ ( v, FloatN ) :: a, ( v, IntN ) :: a ])


{-| The specialisation of the library modules' texts (plans/library-elm-texts.md, L3): each top-level
group whose bindings quantify `number` variables has its default copy and a copy for every other
assignment, so that the module can expose them all (`sum` and `sum$Int`); the module exposes each
value it exposes with its copies.
-}
specialiseLibrary : List ModuleIr -> Inferred -> Result String (List ModuleIr)
specialiseLibrary modules inferred =
    let
        ctx =
            { inferred = inferred, rho = Dict.empty, own = Dict.empty, library = Library.empty }

        requests =
            modules
                |> List.concatMap .defs
                |> List.concatMap declBinders
                |> List.filterMap (\( _, id ) -> groupOf ctx id)
                |> List.concatMap (\( g, vars ) -> List.map (\a -> { group = g, assignment = a }) (allAssignments vars))

        go ms =
            case ms of
                [] ->
                    Ok ( [], requests )

                m :: rest ->
                    scope ctx m.defs (\_ -> go rest)
                        |> Result.map (\( ( defs, inner ), rs ) -> ( defs :: inner, rs ))
    in
    go modules
        |> Result.map
            (\( defsByModule, _ ) ->
                List.map2
                    (\m defs ->
                        let
                            names =
                                List.concatMap declNames defs
                        in
                        { m
                            | defs = defs
                            , exposes =
                                case m.exposes of
                                    ExposeItems items ->
                                        ExposeItems
                                            (List.concatMap
                                                (\item ->
                                                    case item of
                                                        IVar v ->
                                                            IVar v :: List.map IVar (List.filter (String.startsWith (v ++ "$")) names)

                                                        _ ->
                                                            [ item ]
                                                )
                                                items
                                            )

                                    other ->
                                        other
                        }
                    )
                    modules
                    defsByModule
            )
