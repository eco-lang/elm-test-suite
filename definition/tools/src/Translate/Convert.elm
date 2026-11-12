module Translate.Convert exposing (Facts, ModuleSource, Problem, convertProgram, facts)

{-| From elm-syntax's tree of a test to the translator's representation (`Translate.Ir`): name
resolution against the program, its imports and E0, the exact text of literals, the extraction of
`main`'s checks, and every reason the test is outside the fragment the Lean encoding covers
(plans/elm-to-lean-translator.md, B.4 and B.5). The refusal reported is the one of the highest
rank, and among those the first in the source.
-}

import Dict exposing (Dict)
import Elm.Syntax.Declaration as D
import Elm.Syntax.Exposing as X
import Elm.Syntax.Expression as E
import Elm.Syntax.File exposing (File)
import Elm.Syntax.Import exposing (Import)
import Elm.Syntax.Module as M
import Elm.Syntax.Node as Node exposing (Node(..))
import Elm.Syntax.Pattern as P
import Elm.Syntax.Range exposing (Range)
import Elm.Syntax.TypeAnnotation as T
import Regex
import Set exposing (Set)
import Translate.Basis as Basis
import Translate.Directives exposing (Directives)
import Translate.Ir exposing (..)
import Translate.Literal as Literal


type alias Problem =
    { rank : Int, code : String, at : Range }


{-| Ranks, in the order of B.4: effects, imports, constructs, basis, checks.
-}
rankEffects : Int
rankEffects =
    2


rankImport : Int
rankImport =
    3


rankConstruct : Int
rankConstruct =
    4


rankBasis : Int
rankBasis =
    5


rankChecks : Int
rankChecks =
    6


type alias St =
    { next : Int, problems : List Problem }


fresh : St -> ( Int, St )
fresh st =
    ( st.next, { st | next = st.next + 1 } )


problem : Int -> String -> Range -> St -> St
problem rank code at st =
    { st | problems = { rank = rank, code = code, at = at } :: st.problems }


{-| A module's imports: qualifiers to modules, values exposed unqualified (to their module),
constructors exposed unqualified from the program's modules (to their module), and the modules
exposed whole (`exposing (..)`).
-}
type alias Imports =
    { alias : Dict String String
    , exposed : Dict String String
    , exposedCons : Dict String String
    , open : List String
    }


type alias Env =
    { source : String
    , locals : Dict String Int
    , top : Dict String Int
    , cons : Set String
    , recordAliases : Set String
    , imports : Imports
    , exports : Dict String ExportTable
    , prefix : String
    }


{-| The modules a test may import: `Html`, and the default imports restated.
-}
allowedImports : Set String
allowedImports =
    Set.fromList [ "Html", "Basics", "List", "Maybe", "Debug", "Char", "String", "Tuple", "Result", "Platform", "Platform.Cmd", "Platform.Sub", "Task", "Process", "Array", "Bytes", "Json.Encode", "Json.Decode", "VirtualDom" ]


{-| The modules of effects outside the book's basis. Json.Encode and Json.Decode are library
modules (core-library.md): their values are refused as `basis:*`, like any library value.
-}
effectModules : Set String
effectModules =
    Set.fromList [ "Platform", "Platform.Cmd", "Platform.Sub", "Cmd", "Sub", "Task", "Process", "Browser", "Html.Events", "Time", "Http", "Random" ]


{-| The values E0 binds unqualified, and as `Basics.` (B.6).
-}
basicsValues : Set String
basicsValues =
    Set.fromList [ "compare", "not", "xor", "modBy", "remainderBy", "negate", "min", "max", "clamp", "abs", "identity", "always", "isNaN", "isInfinite"
        , "toFloat", "round", "floor", "ceiling", "truncate"
        , "sqrt", "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "e", "pi"
        , "logBase", "degrees", "radians", "turns", "fromPolar", "toPolar", "never"
        ]


basicsConstructors : Set String
basicsConstructors =
    Set.fromList [ "True", "False", "LT", "EQ", "GT" ]


operators : Set String
operators =
    Set.fromList [ "+", "-", "*", "/", "//", "^", "==", "/=", "<", ">", "<=", ">=", "&&", "||", "::", "<<", ">>", "|>", "<|", "++" ]


{-| The default imports' unqualified constructors outside E0, for refusal messages.
-}
defaultConstructorModule : String -> String
defaultConstructorModule k =
    if k == "Ok" || k == "Err" then
        "Result"

    else
        "Basics"


moduleName : List String -> String
moduleName =
    String.join "."


readImports : Dict String ExportTable -> List (Node Import) -> St -> ( Imports, St )
readImports exports imports st0 =
    List.foldl
        (\(Node range imp) ( acc, st ) ->
            let
                name =
                    moduleName (Node.value imp.moduleName)

                user =
                    Dict.get name exports

                st1 =
                    if Set.member name allowedImports || user /= Nothing then
                        st

                    else if Set.member name effectModules then
                        problem rankEffects "effects" range st

                    else
                        problem rankImport ("import:" ++ name) range st

                withAlias =
                    case imp.moduleAlias of
                        Just (Node _ a) ->
                            Dict.insert (moduleName a) name acc.alias

                        Nothing ->
                            acc.alias

                ( ( exposed, exposedCons ), open ) =
                    case Maybe.map Node.value imp.exposingList of
                        Just (X.All _) ->
                            ( ( acc.exposed, acc.exposedCons ), acc.open ++ [ name ] )

                        Just (X.Explicit items) ->
                            ( List.foldl
                                (\(Node _ item) ( d, dc ) ->
                                    case item of
                                        X.FunctionExpose f ->
                                            ( Dict.insert f name d, dc )

                                        X.InfixExpose _ ->
                                            ( d, dc )

                                        X.TypeOrAliasExpose t ->
                                            -- an exposed record alias brings its constructor
                                            case user |> Maybe.andThen (\u -> Dict.get t u.constructors) of
                                                Just _ ->
                                                    ( d, Dict.insert t name dc )

                                                Nothing ->
                                                    ( d, dc )

                                        X.TypeExpose t ->
                                            if t.open /= Nothing then
                                                case user of
                                                    Just u ->
                                                        ( d
                                                        , List.foldl (\k dc2 -> Dict.insert k name dc2)
                                                            dc
                                                            (Dict.get t.name u.typeCons |> Maybe.withDefault [])
                                                        )

                                                    Nothing ->
                                                        ( Dict.insert ("type:" ++ t.name) name d, dc )

                                            else
                                                ( d, dc )
                                )
                                ( acc.exposed, acc.exposedCons )
                                items
                            , acc.open
                            )

                        Nothing ->
                            ( ( acc.exposed, acc.exposedCons ), acc.open )
            in
            ( { alias = withAlias, exposed = exposed, exposedCons = exposedCons, open = open }, st1 )
        )
        ( { alias = Dict.empty, exposed = Dict.empty, exposedCons = Dict.empty, open = [] }, st0 )
        imports


{-| A qualified reference `m.x` (after alias expansion), lower case.
-}
qualifiedValue : String -> String -> Range -> St -> ( Name, St )
qualifiedValue m x range st =
    if Basis.effectValue m x /= Nothing then
        -- a value of Platform, Cmd, Sub, Task or Process (plan step 5)
        ( Global m x, st )

    else if Set.member m effectModules then
        ( Global m x, problem rankEffects "effects" range st )

    else if m == "Basics" && Set.member x basicsValues then
        ( Global "Basics" x, st )

    else if m == "Debug" && (x == "log" || x == "todo" || x == "toString") then
        ( Global "Debug" x, st )

    else if m == "Char" && (x == "toCode" || x == "fromCode") then
        ( Global "Char" x, st )

    else if m == "Html" && x == "text" then
        -- the harness Html (decision D2)
        ( Global "Html" "text", st )

    else
        ( Global m x, problem rankBasis ("basis:" ++ m ++ "." ++ x) range st )


{-| An unqualified reference to `x` that an import of `m` exposes (by its exposing list, explicit
or `(..)`): the value `m.x`, kept unqualified as the source writes it (the module's imports resolve
it, r:dm-import).
-}
unqualifiedValue : String -> String -> Range -> St -> ( Name, St )
unqualifiedValue m x range st =
    case qualifiedValue m x range st of
        ( Global m2 x2, st2 ) ->
            ( Exposed m2 x2, st2 )

        other ->
            other


qualifiedConstructor : String -> String -> Range -> St -> ( Name, St )
qualifiedConstructor m k range st =
    if Set.member m effectModules then
        ( Global m k, problem rankEffects "effects" range st )

    else if m == "Basics" && Set.member k basicsConstructors then
        ( Global "Basics" k, st )

    else if m == "Maybe" && (k == "Just" || k == "Nothing") then
        ( Global "Maybe" k, st )

    else if m == "Result" && (k == "Ok" || k == "Err") then
        ( Global "Result" k, st )

    else
        ( Global m k, problem rankBasis ("basis:" ++ m ++ "." ++ k) range st )


expandAlias : Env -> List String -> String
expandAlias env m =
    let
        name =
            moduleName m
    in
    Dict.get name env.imports.alias |> Maybe.withDefault name


{-| A value of another module of the program, `m.x` (as written: qualified by `qual` or not).
-}
foreignValue : Env -> String -> Maybe String -> String -> Range -> St -> Maybe ( Name, St )
foreignValue env m qual x range st =
    Dict.get m env.exports
        |> Maybe.map
            (\t ->
                case Dict.get x t.values of
                    Just binder ->
                        ( Foreign { binder = binder, qual = qual, name = x }, st )

                    Nothing ->
                        ( Global m x, problem rankImport ("import:" ++ m ++ "." ++ x) range st )
            )


resolveValue : Env -> List String -> String -> Range -> St -> ( Name, St )
resolveValue env qual x range st =
    if not (List.isEmpty qual) then
        case foreignValue env (expandAlias env qual) (Just (moduleName qual)) x range st of
            Just r ->
                r

            Nothing ->
                qualifiedValue (expandAlias env qual) x range st

    else
        case Dict.get x env.locals of
            Just id ->
                ( Local id x, st )

            Nothing ->
                case Dict.get x env.top of
                    Just id ->
                        ( Local id x, st )

                    Nothing ->
                        if Set.member x basicsValues then
                            ( Global "" x, st )

                        else
                            case Dict.get x env.imports.exposed of
                                Just m ->
                                    foreignValue env m Nothing x range st
                                        |> Maybe.withDefault (unqualifiedValue m x range st)

                                Nothing ->
                                    let
                                        -- a module of the program exposed whole that exposes x
                                        userOpen =
                                            env.imports.open
                                                |> List.filter (\m -> Dict.get m env.exports |> Maybe.map (.values >> Dict.member x) |> Maybe.withDefault False)
                                    in
                                    case userOpen of
                                        m :: _ ->
                                            foreignValue env m Nothing x range st
                                                |> Maybe.withDefault (unqualifiedValue m x range st)

                                        [] ->
                                            case List.filter (\m -> m /= "Basics" && not (Dict.member m env.exports)) env.imports.open of
                                                m :: _ ->
                                                    unqualifiedValue m x range st

                                                [] ->
                                                    unqualifiedValue "Basics" x range st


{-| A constructor of another module of the program, as written.
-}
foreignConstructor : Env -> String -> Maybe String -> String -> Range -> St -> Maybe ( Name, St )
foreignConstructor env m qual k range st =
    Dict.get m env.exports
        |> Maybe.map
            (\t ->
                case Dict.get k t.constructors of
                    Just key ->
                        ( ForeignCon { key = key, qual = qual, name = k }, st )

                    Nothing ->
                        ( Global m k, problem rankImport ("import:" ++ m ++ "." ++ k) range st )
            )


resolveConstructor : Env -> List String -> String -> Range -> St -> ( Name, St )
resolveConstructor env qual k range st =
    if not (List.isEmpty qual) then
        case foreignConstructor env (expandAlias env qual) (Just (moduleName qual)) k range st of
            Just r ->
                r

            Nothing ->
                qualifiedConstructor (expandAlias env qual) k range st

    else if Set.member k env.cons then
        ( UserCon (env.prefix ++ k), st )

    else if Set.member k env.recordAliases then
        -- the constructor of a record alias (r:dm-typbind), bound in the module
        ( UserCon (env.prefix ++ k), st )

    else if Dict.member k env.imports.exposedCons then
        Dict.get k env.imports.exposedCons
            |> Maybe.andThen (\m -> foreignConstructor env m Nothing k range st)
            |> Maybe.withDefault ( UserCon k, st )

    else if List.any (\m -> Dict.get m env.exports |> Maybe.map (.constructors >> Dict.member k) |> Maybe.withDefault False) env.imports.open then
        env.imports.open
            |> List.filter (\m -> Dict.get m env.exports |> Maybe.map (.constructors >> Dict.member k) |> Maybe.withDefault False)
            |> List.head
            |> Maybe.andThen (\m -> foreignConstructor env m Nothing k range st)
            |> Maybe.withDefault ( UserCon k, st )

    else if Set.member k basicsConstructors || k == "Just" || k == "Nothing" || k == "Ok" || k == "Err" then
        ( Global "" k, st )

    else
        qualifiedConstructor (defaultConstructorModule k) k range st


checkOperator : String -> Range -> St -> St
checkOperator op range st =
    if Set.member op operators then
        st

    else
        problem rankBasis ("basis:(" ++ op ++ ")") range st


hasSurrogate : String -> Bool
hasSurrogate s =
    String.toList s |> List.any (\c -> Char.toCode c >= 0xD800 && Char.toCode c <= 0xDFFF)



-- PATTERNS


{-| Converts a pattern, giving each variable it binds a fresh id. Returns the variables bound.
-}
pattern : Env -> Node P.Pattern -> St -> ( Pattern, List ( String, Int ), St )
pattern env (Node range p) st =
    case p of
        P.AllPattern ->
            ( PWild, [], st )

        P.UnitPattern ->
            ( PUnit, [], st )

        P.CharPattern c ->
            ( PChar c
            , []
            , if hasSurrogate (String.fromChar c) then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        P.StringPattern s ->
            ( PStr s
            , []
            , if hasSurrogate s then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        P.IntPattern _ ->
            ( PInt (Literal.normaliseDecimal (Literal.textAt env.source range)), [], st )

        P.HexPattern _ ->
            ( PInt (Literal.decimalOfHex (Literal.textAt env.source range)), [], st )

        P.FloatPattern _ ->
            ( PWild, [], problem rankConstruct "construct:float-pattern" range st )

        P.TuplePattern ps ->
            let
                ( qs, bound, st1 ) =
                    patterns env ps st
            in
            ( PTuple qs
            , bound
            , if List.length ps == 2 || List.length ps == 3 then
                st1

              else
                problem rankConstruct "construct:tuple-arity" range st1
            )

        P.RecordPattern fields ->
            List.foldr
                (\(Node _ f) ( acc, bound, s ) ->
                    let
                        ( id, s1 ) =
                            fresh s
                    in
                    ( ( f, id ) :: acc, ( f, id ) :: bound, s1 )
                )
                ( [], [], st )
                fields
                |> (\( fs, bound, s ) -> ( PRecord fs, bound, s ))

        P.UnConsPattern a b ->
            let
                ( qa, ba, st1 ) =
                    pattern env a st

                ( qb, bb, st2 ) =
                    pattern env b st1
            in
            ( PCons qa qb, ba ++ bb, st2 )

        P.ListPattern ps ->
            let
                ( qs, bound, st1 ) =
                    patterns env ps st
            in
            ( PList qs, bound, st1 )

        P.VarPattern x ->
            let
                ( id, st1 ) =
                    fresh st
            in
            ( PVar x id, [ ( x, id ) ], st1 )

        P.NamedPattern ref args ->
            let
                ( name, st1 ) =
                    resolveConstructor env ref.moduleName ref.name range st

                ( qs, bound, st2 ) =
                    patterns env args st1
            in
            ( PCon name qs, bound, st2 )

        P.AsPattern inner (Node _ x) ->
            let
                ( q, bound, st1 ) =
                    pattern env inner st

                ( id, st2 ) =
                    fresh st1
            in
            ( PAs q x id, bound ++ [ ( x, id ) ], st2 )

        P.ParenthesizedPattern inner ->
            let
                ( q, bound, st1 ) =
                    pattern env inner st
            in
            ( PParen q, bound, st1 )


patterns : Env -> List (Node P.Pattern) -> St -> ( List Pattern, List ( String, Int ), St )
patterns env ps st =
    List.foldl
        (\p ( acc, bound, s ) ->
            let
                ( q, b, s1 ) =
                    pattern env p s
            in
            ( acc ++ [ q ], bound ++ b, s1 )
        )
        ( [], [], st )
        ps


bind : List ( String, Int ) -> Env -> Env
bind bound env =
    { env | locals = List.foldl (\( x, id ) d -> Dict.insert x id d) env.locals bound }



-- EXPRESSIONS


expr : Env -> Node E.Expression -> St -> ( Expr, St )
expr env (Node range e) st =
    case e of
        E.UnitExpr ->
            ( EUnit, st )

        E.Application (f :: args) ->
            let
                ( ef, st1 ) =
                    expr env f st

                ( eargs, st2 ) =
                    exprs env args st1
            in
            ( EApp ef eargs, st2 )

        E.Application [] ->
            ( EUnit, problem rankConstruct "construct:empty-application" range st )

        E.OperatorApplication op _ l r ->
            let
                ( occ, st0 ) =
                    fresh (checkOperator op range st)

                ( el, st1 ) =
                    expr env l st0

                ( er, st2 ) =
                    expr env r st1
            in
            ( EBinop occ op el er, st2 )

        E.FunctionOrValue qual x ->
            if String.left 1 x == String.toUpper (String.left 1 x) then
                let
                    ( name, st1 ) =
                        resolveConstructor env qual x range st
                in
                ( ECon name, st1 )

            else
                let
                    ( name, st1 ) =
                        resolveValue env qual x range st

                    ( occ, st2 ) =
                        fresh st1
                in
                ( EVar occ name, st2 )

        E.IfBlock c t f ->
            let
                ( ec, st1 ) =
                    expr env c st

                ( et, st2 ) =
                    expr env t st1

                ( ef, st3 ) =
                    expr env f st2
            in
            case ef of
                EIf arms final ->
                    ( EIf (( ec, et ) :: arms) final, st3 )

                _ ->
                    ( EIf [ ( ec, et ) ] ef, st3 )

        E.PrefixOperator op ->
            let
                ( occ, st1 ) =
                    fresh (checkOperator op range st)
            in
            ( EOp occ op, st1 )

        E.Operator op ->
            ( EOp 0 op, problem rankConstruct ("construct:operator:" ++ op) range st )

        E.Integer _ ->
            let
                ( id, st1 ) =
                    fresh st
            in
            ( EInt id (Literal.normaliseDecimal (Literal.textAt env.source range)), st1 )

        E.Hex _ ->
            let
                ( id, st1 ) =
                    fresh st
            in
            ( EInt id (Literal.decimalOfHex (Literal.textAt env.source range)), st1 )

        E.Floatable _ ->
            case Literal.floatOf (Literal.textAt env.source range) of
                Just f ->
                    ( EFloat f, st )

                Nothing ->
                    ( EUnit, problem rankConstruct "construct:float-literal" range st )

        E.Negation x ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( ENeg ex, st1 )

        E.Literal s ->
            ( EStr s
            , if hasSurrogate s then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        E.CharLiteral c ->
            ( EChar c
            , if hasSurrogate (String.fromChar c) then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        E.TupledExpression xs ->
            let
                ( exs, st1 ) =
                    exprs env xs st
            in
            ( ETuple exs
            , if List.length xs == 2 || List.length xs == 3 then
                st1

              else
                problem rankConstruct "construct:tuple-arity" range st1
            )

        E.ParenthesizedExpression x ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( EParen ex, st1 )

        E.LetExpression block ->
            let
                ( decls, inner, st1 ) =
                    letDecls env block.declarations st

                ( body, st2 ) =
                    expr inner block.expression st1
            in
            ( ELet decls body, st2 )

        E.CaseExpression block ->
            let
                ( scrutinee, st1 ) =
                    expr env block.expression st
            in
            List.foldl
                (\( p, b ) ( acc, s ) ->
                    let
                        ( q, bound, s1 ) =
                            pattern env p s

                        ( eb, s2 ) =
                            expr (bind bound env) b s1
                    in
                    ( acc ++ [ ( q, eb ) ], s2 )
                )
                ( [], st1 )
                block.cases
                |> (\( rules, s ) -> ( ECase scrutinee rules, s ))

        E.LambdaExpression lambda ->
            let
                ( ps, bound, st1 ) =
                    patterns env lambda.args st

                ( body, st2 ) =
                    expr (bind bound env) lambda.expression st1
            in
            ( ELam ps body, st2 )

        E.RecordExpr setters ->
            let
                ( fields, st1 ) =
                    setterList env setters st
            in
            ( ERecord fields, st1 )

        E.ListExpr xs ->
            let
                ( exs, st1 ) =
                    exprs env xs st
            in
            ( EList exs, st1 )

        E.RecordAccess x (Node _ f) ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( EAccess ex f, st1 )

        E.RecordAccessFunction f ->
            ( EAccessor (String.dropLeft 1 f), st )

        E.RecordUpdateExpression (Node r x) setters ->
            let
                ( name, st1 ) =
                    resolveValue env [] x r st

                ( occ, st2 ) =
                    fresh st1

                ( fields, st3 ) =
                    setterList env setters st2
            in
            ( EUpdate occ name fields, st3 )

        E.GLSLExpression _ ->
            ( EUnit, problem rankConstruct "construct:glsl" range st )


exprs : Env -> List (Node E.Expression) -> St -> ( List Expr, St )
exprs env xs st =
    List.foldl
        (\x ( acc, s ) ->
            let
                ( ex, s1 ) =
                    expr env x s
            in
            ( acc ++ [ ex ], s1 )
        )
        ( [], st )
        xs


setterList : Env -> List (Node E.RecordSetter) -> St -> ( List ( String, Expr ), St )
setterList env setters st =
    List.foldl
        (\(Node _ ( Node _ f, x )) ( acc, s ) ->
            let
                ( ex, s1 ) =
                    expr env x s
            in
            ( acc ++ [ ( f, ex ) ], s1 )
        )
        ( [], st )
        setters


{-| The declarations of a `let` (or the top level): first every binder, so that the declarations
may refer to each other, then each right-hand side.
-}
letDecls : Env -> List (Node E.LetDeclaration) -> St -> ( List Decl, Env, St )
letDecls env declarations st =
    let
        -- binders first
        ( heads, st1 ) =
            List.foldl
                (\(Node _ d) ( acc, s ) ->
                    case d of
                        E.LetFunction f ->
                            let
                                ( id, s1 ) =
                                    fresh s
                            in
                            ( acc ++ [ FnHead f id ], s1 )

                        E.LetDestructuring p x ->
                            let
                                ( q, bound, s1 ) =
                                    pattern env p s
                            in
                            ( acc ++ [ PatHead q bound x ], s1 )
                )
                ( [], st )
                declarations

        inner =
            bind
                (List.concatMap
                    (\h ->
                        case h of
                            FnHead f id ->
                                [ ( Node.value (Node.value f.declaration).name, id ) ]

                            PatHead _ bound _ ->
                                bound
                    )
                    heads
                )
                env

        ( decls, st2 ) =
            List.foldl
                (\h ( acc, s ) ->
                    let
                        ( d, s1 ) =
                            declOf inner h s
                    in
                    ( acc ++ [ d ], s1 )
                )
                ( [], st1 )
                heads
    in
    ( decls, inner, st2 )


type Head
    = FnHead E.Function Int
    | PatHead Pattern (List ( String, Int )) (Node E.Expression)


declOf : Env -> Head -> St -> ( Decl, St )
declOf env h st =
    case h of
        FnHead f id ->
            let
                impl =
                    Node.value f.declaration

                ( args, bound, st1 ) =
                    patterns env impl.arguments st

                ( body, st2 ) =
                    expr (bind bound env) impl.expression st1
            in
            ( DFn
                { name = Node.value impl.name
                , binder = id
                , args = args
                , body = body
                , annotation = Maybe.map (Node.value >> .typeAnnotation) f.signature
                }
            , st2
            )

        PatHead q _ x ->
            let
                ( body, st1 ) =
                    expr env x st
            in
            ( DPat q body, st1 )



-- THE MODULE AND MAIN


{-| The literal labels of the `Debug.log` applications in a declaration (in any position, pipes
included: `x |> Debug.log "label"` applies `Debug.log` to its label).
-}
loggedLabels : Decl -> List String
loggedLabels d =
    let
        labelsIn e =
            case e of
                EApp (EVar _ f) ((EStr label) :: _) ->
                    if globalOf f == Just ( "Debug", "log" ) then
                        [ label ]

                    else
                        []

                _ ->
                    []

        collect e =
            labelsIn e ++ List.concatMap collect (children e)
    in
    case d of
        DFn f ->
            collect f.body

        DPat _ x ->
            collect x


{-| A module of a test program, as read: its name, its file, its text and its tree.
-}
type alias ModuleSource =
    { name : String, path : String, source : String, file : File }


{-| The program of a test whose modules are `sources` in program order (the test, its main module,
last), whatever its problems, with every problem, sorted by rank, then position: the first, if
any, is the refusal reported. Binding ids are unique across the program; each module is converted
with the export tables of the modules before it.
-}
convertProgram : Directives -> List ModuleSource -> ( TestProgram, List Problem )
convertProgram directives sources =
    let
        count =
            List.length sources

        ( modules, stEnd ) =
            List.foldl
                (\( i, ms ) ( acc, exports, st ) ->
                    let
                        ( m, table, st1 ) =
                            convertModule exports (i == count - 1) ms st
                    in
                    ( acc ++ [ m ], Dict.insert ms.name table exports, st1 )
                )
                ( [], Dict.empty, { next = 1, problems = [] } )
                (List.indexedMap Tuple.pair sources)
                |> (\( ms, _, st ) -> ( ms, st ))

        mainRange =
            sources
                |> List.reverse
                |> List.head
                |> Maybe.map (\ms -> Node.range ms.file.moduleDefinition)
                |> Maybe.withDefault { start = { row = 0, column = 0 }, end = { row = 0, column = 0 } }

        -- the labels some Debug.log of the program writes as its literal first argument
        logged =
            modules
                |> List.concatMap (\m -> List.concatMap loggedLabels m.defs)
                |> Set.fromList

        stChecked =
            List.foldl
                (\line st ->
                    case lineLabel line of
                        Just label ->
                            if Set.member label logged then
                                st

                            else
                                problem rankChecks ("checks:unmatched:" ++ label) mainRange st

                        Nothing ->
                            st
                )
                stEnd
                directives.lines
    in
    ( { modules = modules, checks = directives.lines, meaning = directives.meaning }
    , stChecked.problems |> List.sortBy (\p -> ( p.rank, p.at.start.row, p.at.start.column ))
    )


exposingOf : X.Exposing -> ExposingIr
exposingOf x =
    case x of
        X.All _ ->
            ExposeAll

        X.Explicit items ->
            ExposeItems
                (List.map
                    (\(Node _ item) ->
                        case item of
                            X.FunctionExpose f ->
                                IVar f

                            X.InfixExpose op ->
                                IOp op

                            X.TypeOrAliasExpose t ->
                                IType t

                            X.TypeExpose t ->
                                if t.open /= Nothing then
                                    IOpen t.name

                                else
                                    IType t.name
                    )
                    items
                )


{-| Whether an exposing list exposes a value, a type by name, a type with its constructors.
-}
exposesValue : ExposingIr -> String -> Bool
exposesValue x name =
    case x of
        ExposeAll ->
            True

        ExposeItems items ->
            List.member (IVar name) items


exposesType : ExposingIr -> String -> Bool
exposesType x name =
    case x of
        ExposeAll ->
            True

        ExposeItems items ->
            List.member (IType name) items || List.member (IOpen name) items


exposesConstructors : ExposingIr -> String -> Bool
exposesConstructors x name =
    case x of
        ExposeAll ->
            True

        ExposeItems items ->
            List.member (IOpen name) items


{-| One module: its representation, its export table, and the state after it.
-}
convertModule : Dict String ExportTable -> Bool -> ModuleSource -> St -> ( ModuleIr, ExportTable, St )
convertModule exports isMain ms st0 =
    let
        source =
            ms.source

        file =
            ms.file

        prefix =
            if isMain then
                ""

            else
                ms.name ++ "."

        moduleRange =
            Node.range file.moduleDefinition

        headerExposing =
            case Node.value file.moduleDefinition of
                M.NormalModule d ->
                    exposingOf (Node.value d.exposingList)

                M.PortModule d ->
                    exposingOf (Node.value d.exposingList)

                M.EffectModule d ->
                    exposingOf (Node.value d.exposingList)

        writtenImports =
            List.map
                (\(Node _ imp) ->
                    { modid = moduleName (Node.value imp.moduleName)
                    , alias = Maybe.map (Node.value >> moduleName) imp.moduleAlias
                    , exposes = Maybe.map (Node.value >> exposingOf) imp.exposingList
                    }
                )
                file.imports

        st1 =
            case Node.value file.moduleDefinition of
                M.PortModule _ ->
                    -- a port module: its ports are declarations of the module (plan step 3)
                    st0

                M.EffectModule _ ->
                    problem rankEffects "effects" moduleRange st0

                M.NormalModule _ ->
                    st0

        ( imports, st2 ) =
            readImports exports file.imports st1

        declarations =
            List.map (\(Node r d) -> ( r, d )) file.declarations

        customTypes =
            List.filterMap
                (\( _, d ) ->
                    case d of
                        D.CustomTypeDeclaration t ->
                            Just t

                        _ ->
                            Nothing
                )
                declarations

        aliasDecls =
            List.filterMap
                (\( _, d ) ->
                    case d of
                        D.AliasDeclaration a ->
                            Just a

                        _ ->
                            Nothing
                )
                declarations

        recordAliases =
            aliasDecls
                |> List.filter
                    (\a ->
                        case Node.value a.typeAnnotation of
                            T.Record _ ->
                                True

                            _ ->
                                False
                    )
                |> List.map (.name >> Node.value)
                |> Set.fromList

        cons =
            List.concatMap
                (\t -> List.map (\(Node _ c) -> ( Node.value c.name, List.length c.arguments )) t.constructors)
                customTypes

        -- a type so large that inference would exhaust the stack (a test of a compiler's limits)
        tooLarge (Node r _) =
            if r.end.row == r.start.row then
                r.end.column - r.start.column > 4000

            else
                r.end.row - r.start.row > 400

        st3 =
            List.foldl
                (\( r, d ) s ->
                    case d of
                        D.PortDeclaration _ ->
                            s

                        D.InfixDeclaration _ ->
                            problem rankConstruct "construct:infix-declaration" r s

                        D.AliasDeclaration a ->
                            if tooLarge a.typeAnnotation then
                                problem rankConstruct "construct:large-type" r s

                            else
                                s

                        D.FunctionDeclaration f ->
                            case f.signature of
                                Just (Node _ sig) ->
                                    if tooLarge sig.typeAnnotation then
                                        problem rankConstruct "construct:large-type" r s

                                    else
                                        s

                                Nothing ->
                                    s

                        _ ->
                            s
                )
                st2
                declarations

        functions =
            List.filterMap
                (\( r, d ) ->
                    case d of
                        D.FunctionDeclaration f ->
                            Just ( r, f )

                        _ ->
                            Nothing
                )
                declarations

        isMainDecl ( _, f ) =
            Node.value (Node.value f.declaration).name == "main"

        mainDecl =
            List.filter isMainDecl functions |> List.head

        -- main is a top-level definition like any other (the module form, plan step 3)
        otherFunctions =
            functions

        destructurings =
            List.filterMap
                (\( r, d ) ->
                    case d of
                        D.Destructuring p x ->
                            Just ( r, p, x )

                        _ ->
                            Nothing
                )
                declarations

        envBase =
            { source = source
            , locals = Dict.empty
            , top = Dict.empty
            , cons = Set.fromList (List.map Tuple.first cons)
            , recordAliases = recordAliases
            , imports = imports
            , exports = exports
            , prefix = prefix
            }

        -- top-level binders
        ( topHeads, st4 ) =
            List.foldl
                (\( _, f ) ( acc, s ) ->
                    let
                        ( id, s1 ) =
                            fresh s
                    in
                    ( acc ++ [ FnHead f id ], s1 )
                )
                ( [], st3 )
                otherFunctions

        ( topPatHeads, st5 ) =
            List.foldl
                (\( _, p, x ) ( acc, s ) ->
                    let
                        ( q, bound, s1 ) =
                            pattern envBase p s
                    in
                    ( acc ++ [ PatHead q bound x ], s1 )
                )
                ( [], st4 )
                destructurings

        allTopHeads =
            topHeads ++ topPatHeads

        -- the ports, each with a binding id: a port binds its name in the module
        ( portDecls, st5b ) =
            List.foldl
                (\( _, d ) ( acc, s ) ->
                    case d of
                        D.PortDeclaration sig ->
                            let
                                ( id, s1 ) =
                                    fresh s
                            in
                            ( acc ++ [ { name = Node.value sig.name, binder = id, annotation = sig.typeAnnotation } ], s1 )

                        _ ->
                            ( acc, s )
                )
                ( [], st5 )
                declarations

        env =
            { envBase
                | top =
                    Dict.fromList
                        (List.map (\pd -> ( pd.name, pd.binder )) portDecls
                            ++ List.concatMap
                            (\h ->
                                case h of
                                    FnHead f id ->
                                        [ ( Node.value (Node.value f.declaration).name, id ) ]

                                    PatHead _ bound _ ->
                                        bound
                            )
                            allTopHeads
                        )
            }

        ( defs, st6 ) =
            List.foldl
                (\h ( acc, s ) ->
                    let
                        ( d, s1 ) =
                            declOf env h s
                    in
                    ( acc ++ [ d ], s1 )
                )
                ( [], st5b )
                allTopHeads

        -- main: a value (no arguments); whether it is a view, Infer decides from its type
        st7 =
            case mainDecl of
                Nothing ->
                    if isMain then
                        problem rankConstruct "construct:main-shape" moduleRange st6

                    else
                        st6

                Just ( r, f ) ->
                    if List.isEmpty (Node.value f.declaration).arguments then
                        st6

                    else
                        problem rankConstruct "construct:main-shape" r st6

        -- what the module exposes to the modules that import it
        ownTypes =
            List.map (\t -> ( Node.value t.name, List.map (\(Node _ c) -> Node.value c.name) t.constructors )) customTypes

        exportTable =
            { values =
                (portDecls
                    |> List.filter (\pd -> exposesValue headerExposing pd.name)
                    |> List.map (\pd -> ( pd.name, pd.binder ))
                )
                    ++ (topHeads
                    |> List.filterMap
                        (\h ->
                            case h of
                                FnHead f id ->
                                    let
                                        x =
                                            Node.value (Node.value f.declaration).name
                                    in
                                    if exposesValue headerExposing x then
                                        Just ( x, id )

                                    else
                                        Nothing

                                PatHead _ _ _ ->
                                    Nothing
                        )
                       )
                    |> Dict.fromList
            , constructors =
                (ownTypes
                    |> List.filter (\( t, _ ) -> exposesConstructors headerExposing t)
                    |> List.concatMap (\( _, ks ) -> List.map (\k -> ( k, prefix ++ k )) ks)
                )
                    ++ (Set.toList recordAliases
                            |> List.filter (exposesType headerExposing)
                            |> List.map (\a -> ( a, prefix ++ a ))
                       )
                    |> Dict.fromList
            , typeCons =
                ownTypes
                    |> List.filter (\( t, _ ) -> exposesConstructors headerExposing t)
                    |> Dict.fromList
            , types =
                ownTypes
                    |> List.filter (\( t, _ ) -> exposesType headerExposing t)
                    |> List.map (\( t, _ ) -> ( t, prefix ++ t ))
                    |> Dict.fromList
            , aliases =
                aliasDecls
                    |> List.filter (\a -> exposesType headerExposing (Node.value a.name))
                    |> List.map (\a -> ( Node.value a.name, { params = List.map Node.value a.generics, annotation = a.typeAnnotation } ))
                    |> Dict.fromList
            }

        -- the types and aliases the module's imports of the program's modules bring in, a later
        -- import's replacing an earlier one's of the same name (sm-item-type)
        ( importedTypes, importedAliases ) =
            List.foldl
                (\imp ( ts, als ) ->
                    case Dict.get imp.modid exports of
                        Just t ->
                            let
                                q =
                                    Maybe.withDefault imp.modid imp.alias

                                qualified =
                                    ( Dict.foldl (\n c d -> Dict.insert (q ++ "." ++ n) c d) ts t.types
                                    , Dict.foldl (\n a d -> Dict.insert (q ++ "." ++ n) a d) als t.aliases
                                    )

                                unqualified ( ts1, als1 ) =
                                    case imp.exposes of
                                        Just ExposeAll ->
                                            ( Dict.union t.types ts1, Dict.union t.aliases als1 )

                                        Just (ExposeItems items) ->
                                            List.foldl
                                                (\item ( d, da ) ->
                                                    case item of
                                                        IType n ->
                                                            ( Dict.get n t.types |> Maybe.map (\c -> Dict.insert n c d) |> Maybe.withDefault d
                                                            , Dict.get n t.aliases |> Maybe.map (\a -> Dict.insert n a da) |> Maybe.withDefault da
                                                            )

                                                        IOpen n ->
                                                            ( Dict.get n t.types |> Maybe.map (\c -> Dict.insert n c d) |> Maybe.withDefault d, da )

                                                        _ ->
                                                            ( d, da )
                                                )
                                                ( ts1, als1 )
                                                items

                                        Nothing ->
                                            ( ts1, als1 )
                            in
                            unqualified qualified

                        Nothing ->
                            ( ts, als )
                )
                ( Dict.empty, Dict.empty )
                writtenImports
    in
    ( { name = ms.name
      , path = ms.path
      , isPort =
            case Node.value file.moduleDefinition of
                M.PortModule _ ->
                    True

                _ ->
                    False
      , exposes = headerExposing
      , imports = writtenImports
      , prefix = prefix
      , cons = cons
      , types =
            Dict.fromList
                (List.map
                    (\t ->
                        ( Node.value t.name
                        , { params = List.map Node.value t.generics
                          , constructors = List.map (\(Node _ c) -> ( Node.value c.name, c.arguments )) t.constructors
                          }
                        )
                    )
                    customTypes
                )
      , aliases =
            Dict.fromList
                (List.map
                    (\a -> ( Node.value a.name, { params = List.map Node.value a.generics, annotation = a.typeAnnotation } ))
                    aliasDecls
                )
      , importedTypes = importedTypes
      , importedAliases = importedAliases
      , ports = portDecls
      , defs = defs
      }
    , exportTable
    , st7
    )


{-| Facts about a test that the report of all refusals records (step 0 of
plans/lean-full-definition.md): the modules it uses beyond the default imports and `Html`, from
its imports and its qualified references; whether `main` applies `Platform.worker`; whether it
is a port module.
-}
type alias Facts =
    { uses : List String, imports : List String, worker : Bool, ports : Bool }


facts : String -> File -> Facts
facts source file =
    let
        imports =
            file.imports |> List.map (\(Node _ i) -> moduleName (Node.value i.moduleName))

        qualified =
            Regex.find qualifiedRef source |> List.filterMap (\m -> List.head m.submatches |> Maybe.andThen identity)

        notDefault m =
            not (List.member m [ "Basics", "List", "Maybe", "Result", "String", "Char", "Tuple", "Debug", "Platform", "Platform.Cmd", "Platform.Sub", "Cmd", "Sub", "Html" ])

        uses =
            (imports ++ qualified) |> List.filter notDefault |> Set.fromList |> Set.toList

        ports =
            case Node.value file.moduleDefinition of
                M.PortModule _ ->
                    True

                _ ->
                    False
    in
    { uses = uses
    , imports = imports
    , worker = String.contains "Platform.worker" source || Regex.contains workerRef source
    , ports = ports
    }


qualifiedRef : Regex.Regex
qualifiedRef =
    Regex.fromString "\\b((?:[A-Z][A-Za-z0-9_]*\\.)*[A-Z][A-Za-z0-9_]*)\\.[a-z][A-Za-z0-9_]*"
        |> Maybe.withDefault Regex.never


workerRef : Regex.Regex
workerRef =
    Regex.fromString "=\\s*worker\\b" |> Maybe.withDefault Regex.never
