module Translate.Convert exposing (Facts, ModuleSource, Problem, convertLibrary, convertProgram, facts)

{-| From eco's tree of a test to the translator's representation (`Translate.Ir`): name
resolution against the program, its imports and E0, the exact text of literals, the extraction of
`main`'s checks, and every reason the test is outside the fragment the Lean encoding covers
(plans/elm-to-lean-translator.md, B.4 and B.5). The refusal reported is the one of the highest
rank, and among those the first in the source.
-}

import Compiler.Core.Annotation as A
import Compiler.Core.Snippet as Snippet
import Compiler.IR.Source as Src
import Compiler.Parse.Declaration as Decl
import Dict exposing (Dict)
import Regex
import Set exposing (Set)
import Translate.Basis as Basis
import Translate.Directives exposing (Directives)
import Translate.Fixity as Fixity
import Translate.Ir exposing (..)
import Translate.Library as Library exposing (Library)
import Translate.Literal as Literal
import Translate.Parse as Parse exposing (Parsed, c1, c2, c2eol)
import Translate.Region as Region exposing (Region)


type alias Problem =
    { rank : Int, code : String, at : Region }


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


problem : Int -> String -> Region -> St -> St
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

    -- the library values the program may name (plans/library-elm-texts.md); `textOfLibrary` when
    -- the module is a library module's text, whose `Elm.Kernel.List.cons` is the list constructor
    , library : Library
    , textOfLibrary : Bool
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
    Set.fromList
        [ "compare"
        , "not"
        , "xor"
        , "modBy"
        , "remainderBy"
        , "negate"
        , "min"
        , "max"
        , "clamp"
        , "abs"
        , "identity"
        , "always"
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
        , "logBase"
        , "degrees"
        , "radians"
        , "turns"
        , "fromPolar"
        , "toPolar"
        , "never"
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


readImports : Dict String ExportTable -> List Parse.Import -> St -> ( Imports, St )
readImports exports imports st0 =
    List.foldl
        (\imp ( acc, st ) ->
            let
                name =
                    imp.name

                -- eco's import has no region: an import starts its line (plans/eco-parser.md, E10)
                range =
                    { start = { row = imp.row, column = 1 }, end = { row = imp.row, column = 1 } }

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
                    case imp.alias of
                        Just a ->
                            Dict.insert a name acc.alias

                        Nothing ->
                            acc.alias

                ( ( exposed, exposedCons ), open ) =
                    case imp.exposing_ of
                        Just (Src.Open _ _) ->
                            ( ( acc.exposed, acc.exposedCons ), acc.open ++ [ name ] )

                        Just (Src.Explicit (A.At _ items)) ->
                            ( List.foldl
                                (\( _, item ) ( d, dc ) ->
                                    case item of
                                        Src.Lower (A.At _ f) ->
                                            ( Dict.insert f name d, dc )

                                        Src.Operator _ _ ->
                                            ( d, dc )

                                        Src.Upper (A.At _ t) ( _, Src.Private ) ->
                                            -- an exposed record alias brings its constructor
                                            case user |> Maybe.andThen (\u -> Dict.get t u.constructors) of
                                                Just _ ->
                                                    ( d, Dict.insert t name dc )

                                                Nothing ->
                                                    ( d, dc )

                                        Src.Upper (A.At _ t) ( _, Src.Public _ ) ->
                                            case user of
                                                Just u ->
                                                    ( d
                                                    , List.foldl (\k dc2 -> Dict.insert k name dc2)
                                                        dc
                                                        (Dict.get t u.typeCons |> Maybe.withDefault [])
                                                    )

                                                Nothing ->
                                                    ( Dict.insert ("type:" ++ t) name d, dc )
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


{-| A qualified reference `m.x` (after alias expansion), lower case. A value of the core library
that the translator evaluates (`Translate.Library`) is a value of the basis.
-}
qualifiedValue : Library -> String -> String -> Region -> St -> ( Name, St )
qualifiedValue lib m x range st =
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

    else if Library.member lib m x then
        -- a value of the core library written in Elm (plans/library-elm-texts.md, L1)
        ( Global m x, st )

    else
        ( Global m x, problem rankBasis ("basis:" ++ m ++ "." ++ x) range st )


{-| An unqualified reference to `x` that an import of `m` exposes (by its exposing list, explicit
or `(..)`): the value `m.x`, kept unqualified as the source writes it (the module's imports resolve
it, r:dm-import).
-}
unqualifiedValue : Library -> String -> String -> Region -> St -> ( Name, St )
unqualifiedValue lib m x range st =
    case qualifiedValue lib m x range st of
        ( Global m2 x2, st2 ) ->
            ( Exposed m2 x2, st2 )

        other ->
            other


qualifiedConstructor : String -> String -> Region -> St -> ( Name, St )
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


expandAlias : Env -> String -> String
expandAlias env name =
    Dict.get name env.imports.alias |> Maybe.withDefault name


{-| A value of another module of the program, `m.x` (as written: qualified by `qual` or not).
-}
foreignValue : Env -> String -> Maybe String -> String -> Region -> St -> Maybe ( Name, St )
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


{-| A value `qual.x` as written; `qual` is "" when it is unqualified.
-}
resolveValue : Env -> String -> String -> Region -> St -> ( Name, St )
resolveValue env qual x range st =
    if qual /= "" then
        case foreignValue env (expandAlias env qual) (Just qual) x range st of
            Just r ->
                r

            Nothing ->
                qualifiedValue env.library (expandAlias env qual) x range st

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
                                        |> Maybe.withDefault (unqualifiedValue env.library m x range st)

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
                                                |> Maybe.withDefault (unqualifiedValue env.library m x range st)

                                        [] ->
                                            case List.filter (\m -> m /= "Basics" && not (Dict.member m env.exports)) env.imports.open of
                                                m :: _ ->
                                                    unqualifiedValue env.library m x range st

                                                [] ->
                                                    unqualifiedValue env.library "Basics" x range st


{-| A constructor of another module of the program, as written.
-}
foreignConstructor : Env -> String -> Maybe String -> String -> Region -> St -> Maybe ( Name, St )
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


resolveConstructor : Env -> String -> String -> Region -> St -> ( Name, St )
resolveConstructor env qual k range st =
    if qual /= "" then
        case foreignConstructor env (expandAlias env qual) (Just qual) k range st of
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


checkOperator : String -> Region -> St -> St
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
pattern : Env -> Src.Pattern -> St -> ( Pattern, List ( String, Int ), St )
pattern env (A.At region p) st =
    let
        range =
            Region.fromA region
    in
    case p of
        Src.PAnything _ ->
            ( PWild, [], st )

        Src.PUnit _ ->
            ( PUnit, [], st )

        Src.PChr text ->
            let
                c =
                    Parse.charValue text
            in
            ( PChar c
            , []
            , if hasSurrogate (String.fromChar c) then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        Src.PStr text _ ->
            let
                v =
                    Parse.stringValue text
            in
            ( PStr v
            , []
            , if hasSurrogate v then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        Src.PInt _ _ ->
            ( PInt (intOf (Literal.textAt env.source range)), [], st )

        Src.PTuple ( _, a ) ( _, b ) rest ->
            let
                ( qs, bound, st1 ) =
                    patterns env (a :: b :: List.map c2 rest) st
            in
            ( PTuple qs, bound, st1 )

        Src.PRecord fields ->
            List.foldr
                (\(A.At _ f) ( acc, bound, s ) ->
                    let
                        ( id, s1 ) =
                            fresh s
                    in
                    ( ( f, id ) :: acc, ( f, id ) :: bound, s1 )
                )
                ( [], [], st )
                (Parse.recordPatternFields fields)
                |> (\( fs, bound, s ) -> ( PRecord fs, bound, s ))

        Src.PCons ( _, a ) ( _, b ) ->
            let
                ( qa, ba, st1 ) =
                    pattern env a st

                ( qb, bb, st2 ) =
                    pattern env b st1
            in
            ( PCons qa qb, ba ++ bb, st2 )

        Src.PList ( _, ps ) ->
            let
                ( qs, bound, st1 ) =
                    patterns env (List.map c2 ps) st
            in
            ( PList qs, bound, st1 )

        Src.PVar x ->
            let
                ( id, st1 ) =
                    fresh st
            in
            ( PVar x id, [ ( x, id ) ], st1 )

        Src.PCtor _ k args ->
            constructorPattern env "" k args range st

        Src.PCtorQual _ qual k args ->
            constructorPattern env qual k args range st

        Src.PAlias ( _, inner ) ( _, A.At _ x ) ->
            let
                ( q, bound, st1 ) =
                    pattern env inner st

                ( id, st2 ) =
                    fresh st1
            in
            ( PAs q x id, bound ++ [ ( x, id ) ], st2 )

        Src.PParens ( _, inner ) ->
            let
                ( q, bound, st1 ) =
                    pattern env inner st
            in
            ( PParen q, bound, st1 )


constructorPattern : Env -> String -> String -> List (Src.C1 Src.Pattern) -> Region -> St -> ( Pattern, List ( String, Int ), St )
constructorPattern env qual k args range st =
    let
        ( name, st1 ) =
            resolveConstructor env qual k range st

        ( qs, bound, st2 ) =
            patterns env (List.map c1 args) st1
    in
    ( PCon name qs, bound, st2 )


{-| An integer constant from its text, exactly: decimal or hexadecimal.
-}
intOf : String -> String
intOf text =
    if String.startsWith "0x" text || String.startsWith "0X" text then
        Literal.decimalOfHex text

    else
        Literal.normaliseDecimal text


patterns : Env -> List Src.Pattern -> St -> ( List Pattern, List ( String, Int ), St )
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


expr : Env -> Src.Expr -> St -> ( Expr, St )
expr env (A.At region e) st =
    let
        range =
            Region.fromA region
    in
    case e of
        Src.Unit ->
            ( EUnit, st )

        Src.Call f a rest ->
            let
                ( ef, st1 ) =
                    expr env f st

                ( eargs, st2 ) =
                    exprs env (List.map c1 (a :: rest)) st1
            in
            ( EApp ef eargs, st2 )

        Src.Binops first rest last ->
            chain env (Fixity.tree first rest last) st

        Src.VarQual _ "Elm.Kernel.List" "cons" ->
            if env.textOfLibrary then
                -- `cons = Elm.Kernel.List.cons` (List.elm): the list constructor, written `(::)`
                -- (plans/library-elm-texts.md, L2)
                let
                    ( occ, st1 ) =
                        fresh st
                in
                ( EOp occ "::", st1 )

            else
                ( EUnit, problem rankBasis "basis:Elm.Kernel.List.cons" range st )

        Src.VarQual _ qual x ->
            variable env qual x range st

        Src.Var _ x ->
            variable env "" x range st

        Src.If ( _, ( ( _, c ), ( _, t ) ) ) rest ( _, f ) ->
            let
                ( arms, st1 ) =
                    List.foldl
                        (\( c_, t_ ) ( acc, s ) ->
                            let
                                ( ec, s1 ) =
                                    expr env c_ s

                                ( et, s2 ) =
                                    expr env t_ s1
                            in
                            ( acc ++ [ ( ec, et ) ], s2 )
                        )
                        ( [], st )
                        (( c, t ) :: List.map (\( _, ( ( _, c_ ), ( _, t_ ) ) ) -> ( c_, t_ )) rest)

                ( ef, st2 ) =
                    expr env f st1
            in
            case ef of
                EIf moreArms final ->
                    ( EIf (arms ++ moreArms) final, st2 )

                _ ->
                    ( EIf arms ef, st2 )

        Src.Op op ->
            let
                ( occ, st1 ) =
                    fresh (checkOperator op range st)
            in
            ( EOp occ op, st1 )

        Src.Int _ _ ->
            let
                ( id, st1 ) =
                    fresh st
            in
            ( EInt id (intOf (Literal.textAt env.source range)), st1 )

        Src.Float _ _ ->
            case Literal.floatOf (Literal.textAt env.source range) of
                Just f ->
                    ( EFloat f, st )

                Nothing ->
                    ( EUnit, problem rankConstruct "construct:float-literal" range st )

        Src.Negate x ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( ENeg ex, st1 )

        Src.Str text _ ->
            let
                v =
                    Parse.stringValue text
            in
            ( EStr v
            , if hasSurrogate v then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        Src.Chr text ->
            let
                c =
                    Parse.charValue text
            in
            ( EChar c
            , if hasSurrogate (String.fromChar c) then
                problem rankConstruct "construct:lone-surrogate" range st

              else
                st
            )

        Src.Tuple ( _, a ) ( _, b ) rest ->
            let
                ( exs, st1 ) =
                    exprs env (a :: b :: List.map c2 rest) st
            in
            ( ETuple exs, st1 )

        Src.Parens ( _, x ) ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( EParen ex, st1 )

        Src.Let defs _ body ->
            let
                ( decls, inner, st1 ) =
                    letDecls env (List.map (c2 >> A.toValue) defs) st

                ( ebody, st2 ) =
                    expr inner body st1
            in
            ( ELet decls ebody, st2 )

        Src.Case ( _, scrutinee ) branches ->
            let
                ( es, st1 ) =
                    expr env scrutinee st
            in
            List.foldl
                (\( ( _, p ), ( _, b ) ) ( acc, s ) ->
                    let
                        ( q, bound, s1 ) =
                            pattern env p s

                        ( eb, s2 ) =
                            expr (bind bound env) b s1
                    in
                    ( acc ++ [ ( q, eb ) ], s2 )
                )
                ( [], st1 )
                branches
                |> (\( rules, s ) -> ( ECase es rules, s ))

        Src.Lambda ( _, args ) ( _, body ) ->
            let
                ( ps, bound, st1 ) =
                    patterns env (List.map c1 args) st

                ( ebody, st2 ) =
                    expr (bind bound env) body st1
            in
            ( ELam ps ebody, st2 )

        Src.Record ( _, setters ) ->
            let
                ( fields, st1 ) =
                    setterList env (List.map c2eol setters) st
            in
            ( ERecord fields, st1 )

        Src.List items _ ->
            let
                ( exs, st1 ) =
                    exprs env (List.map c2eol items) st
            in
            ( EList exs, st1 )

        Src.Access x (A.At _ f) ->
            let
                ( ex, st1 ) =
                    expr env x st
            in
            ( EAccess ex f, st1 )

        Src.Accessor f ->
            ( EAccessor f, st )

        Src.Update ( _, A.At r record ) ( _, ( first, rest ) ) ->
            case record of
                Src.Var _ x ->
                    let
                        ( name, st1 ) =
                            resolveValue env "" x (Region.fromA r) st

                        ( occ, st2 ) =
                            fresh st1

                        ( fields, st3 ) =
                            setterList env (List.map c2eol (first :: rest)) st2
                    in
                    ( EUpdate occ name fields, st3 )

                _ ->
                    -- eco's parser makes the record of an update a lower-case variable
                    ( EUnit, problem rankConstruct "construct:record-update" range st )


{-| A variable or constructor `qual.x` as written (`qual` "" when unqualified).
-}
variable : Env -> String -> String -> Region -> St -> ( Expr, St )
variable env qual x range st =
    if env.textOfLibrary && List.take 2 (String.split "." qual) == [ "Elm", "Kernel" ] then
        -- a library text that names any other kernel value is refused (L2)
        ( EUnit, problem rankBasis ("kernel:" ++ qual ++ "." ++ x) range st )

    else if String.left 1 x == String.toUpper (String.left 1 x) then
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


{-| An operator chain, grouped (`Translate.Fixity`): an operator applied to its two operands.
-}
chain : Env -> Fixity.Tree -> St -> ( Expr, St )
chain env t st =
    case t of
        Fixity.Operand x ->
            expr env x st

        Fixity.Apply a ->
            let
                ( occ, st0 ) =
                    fresh (checkOperator a.op a.region st)

                ( el, st1 ) =
                    chain env a.left st0

                ( er, st2 ) =
                    chain env a.right st1
            in
            ( EBinop occ a.op el er, st2 )


exprs : Env -> List Src.Expr -> St -> ( List Expr, St )
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


setterList : Env -> List ( Src.C1 (A.Located String), Src.C1 Src.Expr ) -> St -> ( List ( String, Expr ), St )
setterList env setters st =
    List.foldl
        (\( ( _, A.At _ f ), ( _, x ) ) ( acc, s ) ->
            let
                ( ex, s1 ) =
                    expr env x s
            in
            ( acc ++ [ ( f, ex ) ], s1 )
        )
        ( [], st )
        setters


{-| A function binding, at the top level or in a `let`: its name, parameters, body and annotation.
-}
type alias Fn =
    { name : String, args : List Src.Pattern, body : Src.Expr, annotation : Maybe Src.Type }


{-| The declarations of a `let` (or the top level): first every binder, so that the declarations
may refer to each other, then each right-hand side.
-}
letDecls : Env -> List Src.Def -> St -> ( List Decl, Env, St )
letDecls env declarations st =
    let
        -- binders first
        ( heads, st1 ) =
            List.foldl
                (\d ( acc, s ) ->
                    case d of
                        Src.Define (A.At _ name) args ( _, body ) tipe ->
                            let
                                ( id, s1 ) =
                                    fresh s
                            in
                            ( acc ++ [ FnHead { name = name, args = List.map c1 args, body = body, annotation = Maybe.map (c1 >> c2) tipe } id ], s1 )

                        Src.Destruct p ( _, x ) ->
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
                                [ ( f.name, id ) ]

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
    = FnHead Fn Int
    | PatHead Pattern (List ( String, Int )) Src.Expr


declOf : Env -> Head -> St -> ( Decl, St )
declOf env h st =
    case h of
        FnHead f id ->
            let
                ( args, bound, st1 ) =
                    patterns env f.args st

                ( body, st2 ) =
                    expr (bind bound env) f.body st1
            in
            ( DFn
                { name = f.name
                , binder = id
                , args = args
                , body = body
                , annotation = f.annotation
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
    { name : String, path : String, source : String, file : Parsed }


{-| The program of a test whose modules are `sources` in program order (the test, its main module,
last), whatever its problems, with every problem, sorted by rank, then position: the first, if
any, is the refusal reported. Binding ids are unique across the program; each module is converted
with the export tables of the modules before it. `lib` is the library values the program may name.
-}
convertProgram : Library -> Directives -> List ModuleSource -> ( TestProgram, List Problem )
convertProgram lib directives sources =
    let
        count =
            List.length sources

        ( modules, stEnd ) =
            List.foldl
                (\( i, ms ) ( acc, exports, st ) ->
                    let
                        ( m, table, st1 ) =
                            convertModule { isMain = i == count - 1, library = lib, textOfLibrary = False } exports ms st
                    in
                    ( acc ++ [ m ], Dict.insert ms.name table exports, st1 )
                )
                ( [], Dict.empty, { next = 1, problems = [] } )
                (List.indexedMap Tuple.pair sources)
                |> (\( ms, _, st ) -> ( ms, st ))

        mainRegion =
            sources
                |> List.reverse
                |> List.head
                |> Maybe.map (\ms -> Parse.headerRegion ms.file)
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
                                problem rankChecks ("checks:unmatched:" ++ label) mainRegion st

                        Nothing ->
                            st
                )
                stEnd
                directives.lines
    in
    ( { modules = modules, checks = directives.lines, meaning = directives.meaning }
    , stChecked.problems |> List.sortBy (\p -> ( p.rank, p.at.start.row, p.at.start.column ))
    )


{-| The texts of the library modules (plans/library-elm-texts.md, step 1), in order, each as
`Translate.Library.textSource` gives it: no module is a main module, and each is converted with the
export tables of the modules before it. Every problem is returned, sorted as for a program.
-}
convertLibrary : List ModuleSource -> ( List ModuleIr, List Problem )
convertLibrary sources =
    let
        ( modules, stEnd ) =
            List.foldl
                (\ms ( acc, exports, st ) ->
                    let
                        ( m, table, st1 ) =
                            convertModule { isMain = False, library = Library.empty, textOfLibrary = True } exports ms st
                    in
                    ( acc ++ [ m ], Dict.insert ms.name table exports, st1 )
                )
                ( [], Dict.empty, { next = 1, problems = [] } )
                sources
                |> (\( ms, _, st ) -> ( ms, st ))
    in
    ( modules, stEnd.problems |> List.sortBy (\p -> ( p.rank, p.at.start.row, p.at.start.column )) )


exposingOf : Src.Exposing -> ExposingIr
exposingOf x =
    case x of
        Src.Open _ _ ->
            ExposeAll

        Src.Explicit (A.At _ items) ->
            ExposeItems
                (List.map
                    (\( _, item ) ->
                        case item of
                            Src.Lower (A.At _ f) ->
                                IVar f

                            Src.Operator _ op ->
                                IOp op

                            Src.Upper (A.At _ t) ( _, Src.Private ) ->
                                IType t

                            Src.Upper (A.At _ t) ( _, Src.Public _ ) ->
                                IOpen t
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


{-| A top-level declaration as the converter reads it, with its region: from its doc comment, if
it has one, to its end (as elm-syntax gave it).
-}
type TopDecl
    = TopFn Region Fn
    | TopType { name : String, params : List String, constructors : List ( String, List Src.Type ) }
    | TopAlias Region { name : String, params : List String, annotation : Src.Type }
    | TopPort { name : String, annotation : Src.Type }


topDecls : Parsed -> List TopDecl
topDecls file =
    let
        regionWithDoc doc r =
            let
                region =
                    Region.fromA r
            in
            case doc of
                Just (Src.Comment (Snippet.Snippet snip)) ->
                    -- the snippet starts after `{-|`
                    { region | start = { row = snip.offRow, column = snip.offCol - 3 } }

                Nothing ->
                    region
    in
    List.map
        (\d ->
            case d of
                Decl.Value doc (A.At r (Src.Value v)) ->
                    TopFn (regionWithDoc doc r)
                        { name = A.toValue (c1 v.name)
                        , args = List.map c1 v.args
                        , body = c1 v.body
                        , annotation = Maybe.map (c1 >> c2) v.tipe
                        }

                Decl.Union _ (A.At _ (Src.Union ( _, A.At _ name ) params first rest)) ->
                    TopType
                        { name = name
                        , params = List.map (c1 >> A.toValue) params
                        , constructors = List.map (\( _, ( A.At _ k, args ) ) -> ( k, List.map c1 args )) (first :: rest)
                        }

                Decl.Alias doc (A.At r (Src.Alias a)) ->
                    TopAlias (regionWithDoc doc r)
                        { name = A.toValue (c2 a.name)
                        , params = List.map (c1 >> A.toValue) a.args
                        , annotation = c1 a.tipe
                        }

                Decl.Port _ (Src.Port _ ( _, A.At _ name ) t) ->
                    TopPort { name = name, annotation = t }
        )
        (Parse.declarations file)


{-| One module: its representation, its export table, and the state after it.
-}
convertModule : { isMain : Bool, library : Library, textOfLibrary : Bool } -> Dict String ExportTable -> ModuleSource -> St -> ( ModuleIr, ExportTable, St )
convertModule mode exports ms st0 =
    let
        isMain =
            mode.isMain

        source =
            ms.source

        file =
            ms.file

        prefix =
            if isMain then
                ""

            else
                ms.name ++ "."

        moduleRegion =
            Parse.headerRegion file

        headerExposing =
            exposingOf (Parse.exposing_ file)

        importList =
            Parse.importsOf file

        writtenImports =
            List.map
                (\imp ->
                    { modid = imp.name
                    , alias = imp.alias
                    , exposes = Maybe.map exposingOf imp.exposing_
                    }
                )
                importList

        ( imports, st2 ) =
            readImports exports importList st0

        declarations =
            topDecls file

        customTypes =
            List.filterMap
                (\d ->
                    case d of
                        TopType t ->
                            Just t

                        _ ->
                            Nothing
                )
                declarations

        aliasDecls =
            List.filterMap
                (\d ->
                    case d of
                        TopAlias _ a ->
                            Just a

                        _ ->
                            Nothing
                )
                declarations

        recordAliases =
            aliasDecls
                |> List.filter (\a -> Parse.recordType a.annotation /= Nothing)
                |> List.map .name
                |> Set.fromList

        cons =
            List.concatMap
                (\t -> List.map (\( k, args ) -> ( k, List.length args )) t.constructors)
                customTypes

        -- a type so large that inference would exhaust the stack (a test of a compiler's limits)
        tooLarge (A.At region _) =
            let
                r =
                    Region.fromA region
            in
            if r.end.row == r.start.row then
                r.end.column - r.start.column > 4000

            else
                r.end.row - r.start.row > 400

        st3 =
            List.foldl
                (\d s ->
                    case d of
                        TopAlias r a ->
                            if tooLarge a.annotation then
                                problem rankConstruct "construct:large-type" r s

                            else
                                s

                        TopFn r f ->
                            case f.annotation of
                                Just t ->
                                    if tooLarge t then
                                        problem rankConstruct "construct:large-type" r s

                                    else
                                        s

                                Nothing ->
                                    s

                        _ ->
                            s
                )
                (List.foldl (\(A.At r _) s -> problem rankConstruct "construct:infix-declaration" (Region.fromA r) s) st2 file.infixes)
                declarations

        functions =
            List.filterMap
                (\d ->
                    case d of
                        TopFn r f ->
                            Just ( r, f )

                        _ ->
                            Nothing
                )
                declarations

        isMainDecl ( _, f ) =
            f.name == "main"

        mainDecl =
            List.filter isMainDecl functions |> List.head

        -- main is a top-level definition like any other (the module form, plan step 3)
        otherFunctions =
            functions

        envBase =
            { source = source
            , locals = Dict.empty
            , top = Dict.empty
            , cons = Set.fromList (List.map Tuple.first cons)
            , recordAliases = recordAliases
            , imports = imports
            , exports = exports
            , prefix = prefix
            , library = mode.library
            , textOfLibrary = mode.textOfLibrary
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

        allTopHeads =
            topHeads

        -- the ports, each with a binding id: a port binds its name in the module
        ( portDecls, st5b ) =
            List.foldl
                (\d ( acc, s ) ->
                    case d of
                        TopPort pd ->
                            let
                                ( id, s1 ) =
                                    fresh s
                            in
                            ( acc ++ [ { name = pd.name, binder = id, annotation = pd.annotation } ], s1 )

                        _ ->
                            ( acc, s )
                )
                ( [], st4 )
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
                                            [ ( f.name, id ) ]

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
                        problem rankConstruct "construct:main-shape" moduleRegion st6

                    else
                        st6

                Just ( r, f ) ->
                    if List.isEmpty f.args then
                        st6

                    else
                        problem rankConstruct "construct:main-shape" r st6

        -- what the module exposes to the modules that import it
        ownTypes =
            List.map (\t -> ( t.name, List.map Tuple.first t.constructors )) customTypes

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
                                            if exposesValue headerExposing f.name then
                                                Just ( f.name, id )

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
                    |> List.filter (\a -> exposesType headerExposing a.name)
                    |> List.map (\a -> ( a.name, { params = a.params, annotation = a.annotation } ))
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
      , isPort = Parse.isPortModule file
      , exposes = headerExposing
      , imports = writtenImports
      , prefix = prefix
      , cons = cons
      , types =
            Dict.fromList
                (List.map
                    (\t -> ( t.name, { params = t.params, constructors = t.constructors } ))
                    customTypes
                )
      , aliases =
            Dict.fromList
                (List.map
                    (\a -> ( a.name, { params = a.params, annotation = a.annotation } ))
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


facts : String -> Parsed -> Facts
facts source file =
    let
        imports =
            Parse.importsOf file |> List.map .name

        qualified =
            Regex.find qualifiedRef source |> List.filterMap (\m -> List.head m.submatches |> Maybe.andThen identity)

        notDefault m =
            not (List.member m [ "Basics", "List", "Maybe", "Result", "String", "Char", "Tuple", "Debug", "Platform", "Platform.Cmd", "Platform.Sub", "Cmd", "Sub", "Html" ])

        uses =
            (imports ++ qualified) |> List.filter notDefault |> Set.fromList |> Set.toList

        ports =
            Parse.isPortModule file
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
