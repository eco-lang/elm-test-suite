module Translate.Convert exposing (Problem, convert)

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
import Set exposing (Set)
import Translate.Directives as Directives exposing (Directives, Expectation(..))
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


type alias Imports =
    { alias : Dict String String
    , exposed : Dict String String
    , open : List String
    }


type alias Env =
    { source : String
    , locals : Dict String Int
    , top : Dict String Int
    , cons : Set String
    , recordAliases : Set String
    , imports : Imports
    }


{-| The modules a test may import: `Html`, and the default imports restated.
-}
allowedImports : Set String
allowedImports =
    Set.fromList [ "Html", "Basics", "List", "Maybe", "Debug", "Char", "String", "Tuple", "Result", "Platform", "Platform.Cmd", "Platform.Sub" ]


effectModules : Set String
effectModules =
    Set.fromList [ "Platform", "Platform.Cmd", "Platform.Sub", "Cmd", "Sub", "Task", "Process", "Browser", "Html.Events", "Json.Decode", "Json.Encode", "Time", "Http", "Random" ]


{-| The values E0 binds unqualified, and as `Basics.` (B.6).
-}
basicsValues : Set String
basicsValues =
    Set.fromList [ "compare", "not", "xor", "modBy", "remainderBy", "negate", "min", "max", "clamp", "abs", "identity", "always", "isNaN", "isInfinite"
        , "toFloat", "round", "floor", "ceiling", "truncate"
        , "sqrt", "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "e", "pi"
        , "append"
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


readImports : List (Node Import) -> St -> ( Imports, St )
readImports imports st0 =
    List.foldl
        (\(Node range imp) ( acc, st ) ->
            let
                name =
                    moduleName (Node.value imp.moduleName)

                st1 =
                    if Set.member name allowedImports then
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

                ( exposed, open ) =
                    case Maybe.map Node.value imp.exposingList of
                        Just (X.All _) ->
                            ( acc.exposed, acc.open ++ [ name ] )

                        Just (X.Explicit items) ->
                            ( List.foldl
                                (\(Node _ item) d ->
                                    case item of
                                        X.FunctionExpose f ->
                                            Dict.insert f name d

                                        X.InfixExpose _ ->
                                            d

                                        X.TypeOrAliasExpose _ ->
                                            d

                                        X.TypeExpose t ->
                                            if t.open /= Nothing then
                                                Dict.insert ("type:" ++ t.name) name d

                                            else
                                                d
                                )
                                acc.exposed
                                items
                            , acc.open
                            )

                        Nothing ->
                            ( acc.exposed, acc.open )
            in
            ( { alias = withAlias, exposed = exposed, open = open }, st1 )
        )
        ( { alias = Dict.empty, exposed = Dict.empty, open = [] }, st0 )
        imports


{-| A qualified reference `m.x` (after alias expansion), lower case.
-}
qualifiedValue : String -> String -> Range -> St -> ( Name, St )
qualifiedValue m x range st =
    if Set.member m effectModules then
        ( Global m x, problem rankEffects "effects" range st )

    else if m == "Basics" && Set.member x basicsValues then
        ( Global "Basics" x, st )

    else if m == "Debug" && (x == "log" || x == "todo" || x == "toString") then
        ( Global "Debug" x, st )

    else if m == "Char" && (x == "toCode" || x == "fromCode") then
        ( Global "Char" x, st )

    else
        ( Global m x, problem rankBasis ("basis:" ++ m ++ "." ++ x) range st )


qualifiedConstructor : String -> String -> Range -> St -> ( Name, St )
qualifiedConstructor m k range st =
    if Set.member m effectModules then
        ( Global m k, problem rankEffects "effects" range st )

    else if m == "Basics" && Set.member k basicsConstructors then
        ( Global "Basics" k, st )

    else if m == "Maybe" && (k == "Just" || k == "Nothing") then
        ( Global "Maybe" k, st )

    else
        ( Global m k, problem rankBasis ("basis:" ++ m ++ "." ++ k) range st )


expandAlias : Env -> List String -> String
expandAlias env m =
    let
        name =
            moduleName m
    in
    Dict.get name env.imports.alias |> Maybe.withDefault name


resolveValue : Env -> List String -> String -> Range -> St -> ( Name, St )
resolveValue env qual x range st =
    if not (List.isEmpty qual) then
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
                                    qualifiedValue m x range st

                                Nothing ->
                                    case List.filter ((/=) "Basics") env.imports.open of
                                        m :: _ ->
                                            qualifiedValue m x range st

                                        [] ->
                                            qualifiedValue "Basics" x range st


resolveConstructor : Env -> List String -> String -> Range -> St -> ( Name, St )
resolveConstructor env qual k range st =
    if not (List.isEmpty qual) then
        qualifiedConstructor (expandAlias env qual) k range st

    else if Set.member k env.cons then
        ( UserCon k, st )

    else if Set.member k env.recordAliases then
        ( UserCon k, problem rankConstruct "construct:record-alias-constructor" range st )

    else if Set.member k basicsConstructors || k == "Just" || k == "Nothing" then
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


isHtmlText : Env -> Node E.Expression -> Bool
isHtmlText env (Node _ e) =
    case e of
        E.Application [ Node _ (E.FunctionOrValue qual "text"), Node _ (E.Literal _) ] ->
            if List.isEmpty qual then
                Dict.get "text" env.imports.exposed == Just "Html" || List.member "Html" env.imports.open

            else
                expandAlias env qual == "Html"

        _ ->
            False


{-| A declaration of `main`'s `let` that logs a check: `_ = Debug.log "label" arg`.
-}
checkOf : Node E.LetDeclaration -> Maybe ( String, Node E.Expression, Range )
checkOf (Node range d) =
    case d of
        E.LetDestructuring (Node _ P.AllPattern) (Node _ (E.Application [ Node _ (E.FunctionOrValue [ "Debug" ] "log"), Node _ (E.Literal label), arg ])) ->
            case arg of
                Node _ (E.ParenthesizedExpression inner) ->
                    Just ( label, inner, range )

                _ ->
                    Just ( label, arg, range )

        _ ->
            Nothing


{-| Logging in another form, which the translator does not take as a check.
-}
otherLogging : Node E.LetDeclaration -> Bool
otherLogging (Node _ d) =
    case d of
        E.LetDestructuring (Node _ P.AllPattern) (Node _ (E.OperatorApplication op _ l r)) ->
            (op == "|>" || op == "<|") && (mentionsLog l || mentionsLog r)

        _ ->
            False


mentionsLog : Node E.Expression -> Bool
mentionsLog (Node _ e) =
    case e of
        E.FunctionOrValue [ "Debug" ] "log" ->
            True

        E.Application xs ->
            List.any mentionsLog xs

        E.ParenthesizedExpression x ->
            mentionsLog x

        _ ->
            False


convert : String -> Directives -> File -> Result Problem TestProgram
convert source directives file =
    let
        st0 =
            { next = 1, problems = [] }

        moduleRange =
            Node.range file.moduleDefinition

        st1 =
            case Node.value file.moduleDefinition of
                M.PortModule _ ->
                    problem rankEffects "effects" moduleRange st0

                M.EffectModule _ ->
                    problem rankEffects "effects" moduleRange st0

                M.NormalModule _ ->
                    st0

        ( imports, st2 ) =
            readImports file.imports st1

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
                            problem rankEffects "effects" r s

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

        isMain ( _, f ) =
            Node.value (Node.value f.declaration).name == "main"

        mainDecl =
            List.filter isMain functions |> List.head

        otherFunctions =
            List.filter (not << isMain) functions

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

        env =
            { envBase
                | top =
                    Dict.fromList
                        (List.concatMap
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
                ( [], st5 )
                allTopHeads

        ( localsAndChecks, st7 ) =
            case mainDecl of
                Nothing ->
                    ( ( [], [] ), problem rankConstruct "construct:main-shape" moduleRange st6 )

                Just ( r, f ) ->
                    let
                        impl =
                            Node.value f.declaration
                    in
                    case ( impl.arguments, impl.expression ) of
                        ( [], Node _ (E.LetExpression block) ) ->
                            let
                                st6a =
                                    if isHtmlText env block.expression then
                                        st6

                                    else
                                        problem rankConstruct "construct:main-shape" (Node.range block.expression) st6

                                ( checkDecls, localDecls ) =
                                    List.partition (\d -> checkOf d /= Nothing) block.declarations

                                st6b =
                                    List.foldl
                                        (\d s ->
                                            if otherLogging d then
                                                problem rankConstruct "construct:check-shape" (Node.range d) s

                                            else
                                                s
                                        )
                                        st6a
                                        localDecls

                                ( locals, inner, st6c ) =
                                    letDecls env localDecls st6b

                                ( checksFound, st6d ) =
                                    List.foldl
                                        (\d ( acc, s ) ->
                                            case checkOf d of
                                                Just ( label, arg, _ ) ->
                                                    let
                                                        ( ex, s1 ) =
                                                            expr inner arg s
                                                    in
                                                    ( acc ++ [ ( label, ex, Node.range d ) ], s1 )

                                                Nothing ->
                                                    ( acc, s )
                                        )
                                        ( [], st6c )
                                        checkDecls
                            in
                            ( ( locals, checksFound ), st6d )

                        _ ->
                            ( ( [], [] ), problem rankConstruct "construct:main-shape" r st6 )

        ( locals0, rawChecks ) =
            localsAndChecks

        -- checks against the CHECK lines, one to one
        labels =
            List.map (\( l, _, _ ) -> l) rawChecks

        st8 =
            List.foldl
                (\( label, _, r ) s ->
                    if List.length (List.filter ((==) label) labels) > 1 then
                        problem rankChecks ("checks:unmatched:" ++ label) r s

                    else if Dict.member label directives.expected then
                        s

                    else
                        problem rankChecks ("checks:unmatched:" ++ label) r s
                )
                st7
                rawChecks

        st9 =
            List.foldl
                (\label s ->
                    if List.member label labels then
                        s

                    else
                        problem rankChecks ("checks:unmatched:" ++ label) moduleRange s
                )
                st8
                directives.labelsInOrder

        checks =
            List.map
                (\( label, ex, _ ) ->
                    { label = label
                    , expected =
                        case Dict.get label directives.expected of
                            Just (Value v) ->
                                v

                            Just NoValue ->
                                "(no value)"

                            Nothing ->
                                ""
                    , expr = ex
                    }
                )
                rawChecks

        best =
            st9.problems
                |> List.sortBy (\p -> ( p.rank, p.at.start.row, p.at.start.column ))
                |> List.head
    in
    case best of
        Just p ->
            Err p

        Nothing ->
            Ok
                { cons = cons
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
                , defs = defs
                , locals = locals0
                , checks = checks
                }
