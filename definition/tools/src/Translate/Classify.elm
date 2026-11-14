module Translate.Classify exposing
    ( ErrorRecord
    , ModuleParse
    , Refs
    , SuccessRecord
    , bookLabels
    , classifyError
    , classifySuccess
    , emptyRefs
    , functionRefs
    , furtherRules
    , syntacticRules
    , trustedRules
    )

{-| The static classification of the `elm-spec` tests (plans/lean-full-definition/step-07-classify.md,
sections 2 and 3). Pure: `Translate.elm` reads the files and parses them.

A compile-error test gets one class, by the first rule that applies: its program does not parse
(`parse-fail`); its rule is a restriction trusted to the parser (`lexical-accepted`); a restriction
decidable on a syntax tree (`syntactic`, step 8); exhaustiveness or irredundancy (`further`, step 9);
the fixities (`fixity-inference`, step 11); a test the override table puts among those refused
without inference (`static-deterministic`, step 9); otherwise `inference` (step 11).

A compile-success test records what it needs beyond the book's basis B0: its helper modules, the
harness's `Html.text`, library values of modules of ME0 that Appendix C does not bind, and modules
outside ME0; its `basis` is the first of those that applies.

-}

import Dict exposing (Dict)
import Elm.Syntax.Declaration exposing (Declaration(..))
import Elm.Syntax.Exposing exposing (Exposing(..), TopLevelExpose(..))
import Elm.Syntax.Expression exposing (Expression(..), Function, LetDeclaration(..))
import Elm.Syntax.File exposing (File)
import Elm.Syntax.Import exposing (Import)
import Elm.Syntax.Node as Node exposing (Node(..))
import Elm.Syntax.Pattern exposing (Pattern(..))
import Elm.Syntax.Range
import Elm.Syntax.TypeAnnotation exposing (TypeAnnotation(..))
import Set exposing (Set)
import StaticBasis.Json as SB
import Translate.ClassifyOverrides exposing (Override)


{-| A module of a test's program, by its path, parsed or not.
-}
type alias ModuleParse =
    { path : String, name : String, file : Maybe File }


type alias ErrorRecord =
    { project : String
    , name : String
    , modules : List ( String, Bool )
    , parse : Bool
    , rules : List String
    , rule : Maybe String
    , class : String
    , subclass : Maybe String
    , step : Maybe Int
    , trust : List String
    , title : Maybe String
    , override : Maybe String
    }


type alias SuccessRecord =
    { project : String
    , name : String
    , modules : List ( String, Bool )
    , parse : Bool
    , basis : String
    , needs : List String
    , main : String
    , mainAnnotated : Bool
    }



-- BOOK LABELS


{-| Every argument of `\label{...}`, `\citelabel{...}`, `\citealso{...}` and `\defnrule[...]` of a
text.
-}
bookLabels : String -> Set String
bookLabels tex =
    let
        args _ close prefix =
            String.split prefix tex
                |> List.drop 1
                |> List.filterMap
                    (\rest ->
                        case String.indexes close rest of
                            i :: _ ->
                                Just (String.left i rest)

                            [] ->
                                Nothing
                    )
    in
    (args "{" "}" "\\label{"
        ++ args "{" "}" "\\citelabel{"
        ++ args "{" "}" "\\citealso{"
        ++ args "[" "]" "\\defnrule["
    )
        |> Set.fromList



-- COMPILE-ERROR TESTS


{-| The nine restrictions trusted to the parser (plan, "Out of scope").
-}
trustedRules : List String
trustedRules =
    [ "res:core-escape-unicode"
    , "res:core-identifier-characters"
    , "res:core-constant-separated"
    , "res:core-adjacent-items"
    , "res:core-layout-rule"
    , "res:core-operator-chain"
    , "res:core-field-selection"
    , "res:core-annotation-placement"
    , "res:modules-header"
    ]


{-| The 27 restrictions decidable on a syntax tree (step 8, section 5).
-}
syntacticRules : List String
syntacticRules =
    [ "res:core-row-labels-distinct"
    , "res:core-record-update-form"
    , "res:core-binding-site-distinct"
    , "res:core-no-shadowing"
    , "res:core-no-float-pattern"
    , "res:core-let-recursion"
    , "res:modules-ports"
    , "res:modules-import-alias"
    , "res:modules-basics-qualifier"
    , "res:modules-no-operator-exposing"
    , "res:modules-header-exposing"
    , "res:modules-exposing-distinct"
    , "res:modules-no-top-pattern"
    , "res:modules-values-distinct"
    , "res:modules-types-distinct"
    , "res:modules-constructors-distinct"
    , "res:modules-no-shadowing"
    , "res:modules-tyvarseq-distinct"
    , "res:modules-custom-type-tyvars"
    , "res:modules-alias-tyvars"
    , "res:modules-alias-not-recursive"
    , "res:modules-value-recursion"
    , "res:modules-program"
    , "res:program-modules-distinct"
    , "res:program-import-order"
    , "res:program-modules-reachable"
    , "res:program-main"
    ]


furtherRules : List String
furtherRules =
    [ "res:core-exhaustiveness", "res:core-irredundancy" ]


{-| A tag t resolves to the first of r:t, <res:t>, t that is a label of the book.
-}
resolveTag : Set String -> String -> Maybe String
resolveTag labels t =
    [ "r:" ++ t, "res:" ++ t, t ] |> List.filter (\l -> Set.member l labels) |> List.head


classifyError :
    { labels : Set String, overrides : List Override }
    -> { project : String, name : String, tags : List String, title : Maybe String, modules : List ModuleParse }
    -> ErrorRecord
classifyError ctx t =
    let
        parses =
            List.all (\m -> m.file /= Nothing) t.modules

        rules =
            List.filterMap (resolveTag ctx.labels) t.tags

        ov =
            ctx.overrides |> List.filter (\o -> o.name == t.name) |> List.head

        rule =
            case ov |> Maybe.andThen .rule of
                Just r ->
                    Just r

                Nothing ->
                    List.head rules

        isIn list =
            rule |> Maybe.map (\r -> List.member r list) |> Maybe.withDefault False

        ( class, subclass ) =
            if not parses then
                ( "parse-fail", Nothing )

            else if isIn trustedRules then
                ( "lexical-accepted", Nothing )

            else if isIn syntacticRules then
                ( "syntactic", Nothing )

            else if isIn furtherRules then
                ( "further", Nothing )

            else if rule == Just "fig:core-fixities" then
                ( "fixity-inference", Nothing )

            else
                case ov of
                    Just o ->
                        ( o.class, o.subclass )

                    Nothing ->
                        ( "inference", Nothing )

        ( step, trust ) =
            case class of
                "syntactic" ->
                    ( Just 8, [ "parse" ] )

                "further" ->
                    ( Just 9, [ "parse", "params" ] )

                "static-deterministic" ->
                    ( Just 9, [ "parse", "harness" ] )

                "fixity-inference" ->
                    ( Just 11, [ "parse" ] )

                "inference" ->
                    ( Just 11, [ "parse", "harness" ] )

                _ ->
                    ( Nothing, [] )
    in
    { project = t.project
    , name = t.name
    , modules = List.map (\m -> ( m.path, m.file /= Nothing )) t.modules
    , parse = parses
    , rules = rules
    , rule = rule
    , class = class
    , subclass = subclass
    , step = step
    , trust = trust
    , title = t.title
    , override = ov |> Maybe.map .note
    }



-- COMPILE-SUCCESS TESTS


type alias Imp =
    { mod : String, alias_ : Maybe String, exposing_ : Maybe Exposing }


importsOf : List SB.DefaultImport -> File -> List Imp
importsOf defaults file =
    List.map
        (\d ->
            { mod = d.module_
            , alias_ = d.as_
            , exposing_ =
                case d.exposing_ of
                    Just SB.ExposingAll ->
                        Just (All Elm.Syntax.Range.emptyRange)

                    Just (SB.ExposingItems items) ->
                        Just
                            (Explicit
                                (List.map
                                    (\it ->
                                        Node Elm.Syntax.Range.emptyRange
                                            (case it of
                                                SB.ExpValue x ->
                                                    FunctionExpose x

                                                SB.ExpOp o ->
                                                    InfixExpose o

                                                SB.ExpType ty ->
                                                    TypeOrAliasExpose ty

                                                SB.ExpTypeAll ty ->
                                                    TypeExpose { name = ty, open = Just Elm.Syntax.Range.emptyRange }
                                            )
                                    )
                                    items
                                )
                            )

                    Nothing ->
                        Nothing
            }
        )
        defaults
        ++ List.map
            (\(Node _ i) ->
                { mod = String.join "." (Node.value i.moduleName)
                , alias_ = i.moduleAlias |> Maybe.map (Node.value >> String.join ".")
                , exposing_ = i.exposingList |> Maybe.map Node.value
                }
            )
            file.imports


{-| The names an interface binds: its values, its type constructors and their constructors.
-}
interfaceNames : SB.Basis -> String -> Maybe (Set String)
interfaceNames basis m =
    basis.modules
        |> List.filter (\i -> i.module_ == m)
        |> List.head
        |> Maybe.map
            (\i ->
                Set.fromList
                    (List.map .name i.ve
                        ++ List.map .tycon i.te
                        ++ List.concatMap (.ve >> List.map .name) i.te
                    )
            )


type alias Refs =
    { qualified : List ( String, String ), unqualified : List String, binders : Set String }


emptyRefs : Refs
emptyRefs =
    { qualified = [], unqualified = [], binders = Set.empty }


addRef : List String -> String -> Refs -> Refs
addRef mn x r =
    if List.isEmpty mn then
        { r | unqualified = x :: r.unqualified }

    else
        { r | qualified = ( String.join "." mn, x ) :: r.qualified }


bind : String -> Refs -> Refs
bind x r =
    { r | binders = Set.insert x r.binders }


exprRefs : Node Expression -> Refs -> Refs
exprRefs (Node _ e) r =
    case e of
        Application es ->
            List.foldl exprRefs r es

        OperatorApplication _ _ a b ->
            exprRefs b (exprRefs a r)

        FunctionOrValue mn x ->
            addRef mn x r

        IfBlock a b c ->
            exprRefs c (exprRefs b (exprRefs a r))

        Negation a ->
            exprRefs a r

        TupledExpression es ->
            List.foldl exprRefs r es

        ParenthesizedExpression a ->
            exprRefs a r

        LetExpression lb ->
            exprRefs lb.expression
                (List.foldl
                    (\(Node _ d) acc ->
                        case d of
                            LetFunction f ->
                                functionRefs f acc

                            LetDestructuring p x ->
                                exprRefs x (patRefs p acc)
                    )
                    r
                    lb.declarations
                )

        CaseExpression cb ->
            List.foldl (\( p, x ) acc -> exprRefs x (patRefs p acc)) (exprRefs cb.expression r) cb.cases

        LambdaExpression l ->
            exprRefs l.expression (List.foldl patRefs r l.args)

        RecordExpr setters ->
            List.foldl (\(Node _ ( _, x )) acc -> exprRefs x acc) r setters

        ListExpr es ->
            List.foldl exprRefs r es

        RecordAccess a _ ->
            exprRefs a r

        RecordUpdateExpression (Node _ x) setters ->
            List.foldl (\(Node _ ( _, v )) acc -> exprRefs v acc) (addRef [] x r) setters

        _ ->
            r


patRefs : Node Pattern -> Refs -> Refs
patRefs (Node _ p) r =
    case p of
        TuplePattern ps ->
            List.foldl patRefs r ps

        RecordPattern fs ->
            List.foldl (\(Node _ f) acc -> bind f acc) r fs

        UnConsPattern a b ->
            patRefs b (patRefs a r)

        ListPattern ps ->
            List.foldl patRefs r ps

        VarPattern x ->
            bind x r

        NamedPattern q ps ->
            List.foldl patRefs (addRef q.moduleName q.name r) ps

        AsPattern a (Node _ x) ->
            bind x (patRefs a r)

        ParenthesizedPattern a ->
            patRefs a r

        _ ->
            r


typeRefs : Node TypeAnnotation -> Refs -> Refs
typeRefs (Node _ t) r =
    case t of
        Typed (Node _ ( mn, x )) args ->
            List.foldl typeRefs (addRef mn x r) args

        Tupled ts ->
            List.foldl typeRefs r ts

        Record fs ->
            List.foldl (\(Node _ ( _, ft )) acc -> typeRefs ft acc) r fs

        GenericRecord _ (Node _ fs) ->
            List.foldl (\(Node _ ( _, ft )) acc -> typeRefs ft acc) r fs

        FunctionTypeAnnotation a b ->
            typeRefs b (typeRefs a r)

        _ ->
            r


functionRefs : Function -> Refs -> Refs
functionRefs f r =
    let
        impl =
            Node.value f.declaration

        withSig =
            case f.signature of
                Just (Node _ s) ->
                    typeRefs s.typeAnnotation r

                Nothing ->
                    r
    in
    exprRefs impl.expression (List.foldl patRefs (bind (Node.value impl.name) withSig) impl.arguments)


moduleRefs : File -> Refs
moduleRefs file =
    List.foldl
        (\(Node _ d) acc ->
            case d of
                FunctionDeclaration f ->
                    functionRefs f acc

                AliasDeclaration a ->
                    typeRefs a.typeAnnotation (bind (Node.value a.name) acc)

                CustomTypeDeclaration ty ->
                    List.foldl
                        (\(Node _ c) acc2 -> List.foldl typeRefs (bind (Node.value c.name) acc2) c.arguments)
                        (bind (Node.value ty.name) acc)
                        ty.constructors

                PortDeclaration s ->
                    typeRefs s.typeAnnotation (bind (Node.value s.name) acc)

                Destructuring p x ->
                    exprRefs x (patRefs p acc)

                _ ->
                    acc
        )
        emptyRefs
        file.declarations


exposes : Exposing -> String -> Bool
exposes ex x =
    case ex of
        All _ ->
            True

        Explicit items ->
            List.any
                (\(Node _ it) ->
                    case it of
                        FunctionExpose y ->
                            y == x

                        TypeOrAliasExpose y ->
                            y == x

                        TypeExpose et ->
                            et.name == x

                        InfixExpose _ ->
                            False
                )
                items


exposesExplicitly : Exposing -> String -> Bool
exposesExplicitly ex x =
    case ex of
        All _ ->
            False

        Explicit _ ->
            exposes ex x


{-| What one module needs: `harness`, `library:M.x`, `outside:M` (helpers are added by the caller).
-}
moduleNeeds : SB.Basis -> Set String -> File -> List String
moduleNeeds basis helpers file =
    let
        imps =
            importsOf basis.defaultImports file

        inME0 m =
            interfaceNames basis m /= Nothing

        outside =
            file.imports
                |> List.map (\(Node _ i) -> String.join "." (Node.value i.moduleName))
                |> List.filter (\m -> not (inME0 m) && not (Set.member m helpers))
                |> List.map (\m -> "outside:" ++ m)

        refs =
            moduleRefs file

        use m x =
            if Set.member m helpers then
                []

            else
                case interfaceNames basis m of
                    Just names ->
                        if m == "Html" && x == "text" then
                            [ "harness" ]

                        else if Set.member x names then
                            []

                        else
                            [ "library:" ++ m ++ "." ++ x ]

                    Nothing ->
                        []

        qualifiedNeeds =
            refs.qualified
                |> List.concatMap
                    (\( q, x ) ->
                        imps
                            |> List.filter (\i -> i.alias_ == Just q || (i.alias_ == Nothing && i.mod == q))
                            |> List.head
                            |> Maybe.map (\i -> use i.mod x)
                            |> Maybe.withDefault []
                    )

        unqualifiedNeeds =
            refs.unqualified
                |> List.filter (\x -> not (Set.member x refs.binders) && not (List.member x [ "List", "[]", "::" ]))
                |> List.concatMap
                    (\x ->
                        let
                            explicit =
                                imps |> List.filter (\i -> i.exposing_ |> Maybe.map (\ex -> exposesExplicitly ex x) |> Maybe.withDefault False)

                            viaAll =
                                imps
                                    |> List.filter (\i -> i.exposing_ |> Maybe.map (\ex -> isAll ex) |> Maybe.withDefault False)
                                    |> List.filter (\i -> interfaceNames basis i.mod |> Maybe.map (Set.member x) |> Maybe.withDefault False)
                        in
                        case ( explicit, viaAll ) of
                            ( i :: _, _ ) ->
                                use i.mod x

                            ( [], _ :: _ ) ->
                                []

                            ( [], [] ) ->
                                -- a value an `exposing (..)` of a library module may supply
                                imps
                                    |> List.filter (\_ -> String.left 1 x == String.toLower (String.left 1 x))
                                    |> List.filter (\i -> i.mod /= "Basics" && (i.exposing_ |> Maybe.map isAll |> Maybe.withDefault False))
                                    |> List.filter (\i -> inME0 i.mod && not (Set.member i.mod helpers))
                                    |> List.head
                                    |> Maybe.map (\i -> use i.mod x)
                                    |> Maybe.withDefault []
                    )
    in
    outside ++ qualifiedNeeds ++ unqualifiedNeeds


isAll : Exposing -> Bool
isAll ex =
    case ex of
        All _ ->
            True

        _ ->
            False


{-| The shape of `main` in the main module: "view" (an application spine of `text`), "program"
(of `Platform.worker`), or "other"; and whether it is annotated.
-}
mainShape : File -> ( String, Bool )
mainShape file =
    file.declarations
        |> List.filterMap
            (\(Node _ d) ->
                case d of
                    FunctionDeclaration f ->
                        if Node.value (Node.value f.declaration).name == "main" then
                            Just ( shapeOf (Node.value f.declaration).expression, f.signature /= Nothing )

                        else
                            Nothing

                    _ ->
                        Nothing
            )
        |> List.head
        |> Maybe.withDefault ( "other", False )


shapeOf : Node Expression -> String
shapeOf (Node _ e) =
    case e of
        Application (h :: _) ->
            shapeOf h

        ParenthesizedExpression a ->
            shapeOf a

        OperatorApplication "<|" _ a _ ->
            shapeOf a

        OperatorApplication "|>" _ _ b ->
            shapeOf b

        FunctionOrValue mn x ->
            if x == "text" && (mn == [] || mn == [ "Html" ]) then
                "view"

            else if x == "worker" && (mn == [ "Platform" ] || mn == []) then
                "program"

            else
                "other"

        _ ->
            "other"


classifySuccess :
    SB.Basis
    -> { project : String, name : String, modules : List ModuleParse, helpers : Set String }
    -> SuccessRecord
classifySuccess basis t =
    let
        parses =
            List.all (\m -> m.file /= Nothing) t.modules

        helperNeeds =
            t.modules
                |> List.filter (\m -> m.name /= t.name)
                |> List.map (\m -> "helper:" ++ m.name)

        needs =
            (helperNeeds
                ++ List.concatMap (\m -> m.file |> Maybe.map (moduleNeeds basis t.helpers) |> Maybe.withDefault []) t.modules
            )
                |> unique

        has p =
            List.any (String.startsWith p) needs

        basisClass =
            if not parses then
                "parse-fail"

            else if has "outside:" then
                "outside"

            else if has "helper:" then
                "helper"

            else if has "library:" then
                "library"

            else if List.member "harness" needs then
                "harness"

            else
                "B0"

        ( shape, annotated ) =
            t.modules
                |> List.filter (\m -> m.name == t.name)
                |> List.head
                |> Maybe.andThen .file
                |> Maybe.map mainShape
                |> Maybe.withDefault ( "other", False )
    in
    { project = t.project
    , name = t.name
    , modules = List.map (\m -> ( m.path, m.file /= Nothing )) t.modules
    , parse = parses
    , basis = basisClass
    , needs = needs
    , main = shape
    , mainAnnotated = annotated
    }


unique : List String -> List String
unique =
    List.foldl
        (\x acc ->
            if List.member x acc then
                acc

            else
                acc ++ [ x ]
        )
        []
