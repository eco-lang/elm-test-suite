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
(`parse-fail`); the translator's front end refuses it (`syntax-refused`, `Translate.FrontEnd`, with
the reason as its subclass); its rule is a restriction trusted to the parser (`lexical-accepted`); a restriction
decidable on a syntax tree (`syntactic`, step 8); exhaustiveness or irredundancy (`further`, step 9);
the fixities (`fixity-inference`, step 11); a test the override table puts among those refused
without inference (`static-deterministic`, step 9); otherwise `inference` (step 11).

A compile-success test records what it needs beyond the book's basis B0: its helper modules, the
harness's `Html.text`, library values of modules of ME0 that Appendix C does not bind, and modules
outside ME0; its `basis` is the first of those that applies.

-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Compiler.Parse.Declaration as Decl
import Dict exposing (Dict)
import Set exposing (Set)
import StaticBasis.Json as SB
import Translate.ClassifyOverrides exposing (Override)
import Translate.Fixity as Fixity
import Translate.Parse as Parse exposing (Function, Parsed, c1, c2, c2eol)


{-| A module of a test's program, by its path, parsed or not; and why it is refused, if it is: it
does not parse (`file` is `Nothing`), or the translator's front end refuses it (`Translate.FrontEnd`).
-}
type alias ModuleParse =
    { path : String
    , name : String
    , file : Maybe Parsed
    , refusal : Maybe { reason : String, at : String, detail : Maybe String }
    }


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

        syntax =
            t.modules
                |> List.filterMap
                    (\m ->
                        if m.file /= Nothing then
                            Maybe.map .reason m.refusal

                        else
                            Nothing
                    )
                |> List.head

        ( class, subclass ) =
            if not parses then
                ( "parse-fail", Nothing )

            else if syntax /= Nothing then
                ( "syntax-refused", syntax )

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


{-| An exposing list as the classification reads it: `(..)`, or the names of the values and types
it lists.
-}
type Exposing
    = All
    | Explicit (List String)


exposingOf : Src.Exposing -> Exposing
exposingOf ex =
    case ex of
        Src.Open _ _ ->
            All

        Src.Explicit (A.At _ items) ->
            Explicit
                (List.filterMap
                    (\( _, it ) ->
                        case it of
                            Src.Lower (A.At _ x) ->
                                Just x

                            Src.Upper (A.At _ x) _ ->
                                Just x

                            Src.Operator _ _ ->
                                Nothing
                    )
                    items
                )


importsOf : List SB.DefaultImport -> Parsed -> List Imp
importsOf defaults file =
    List.map
        (\d ->
            { mod = d.module_
            , alias_ = d.as_
            , exposing_ =
                case d.exposing_ of
                    Just SB.ExposingAll ->
                        Just All

                    Just (SB.ExposingItems items) ->
                        Just
                            (Explicit
                                (List.filterMap
                                    (\it ->
                                        case it of
                                            SB.ExpValue x ->
                                                Just x

                                            SB.ExpOp _ ->
                                                Nothing

                                            SB.ExpType ty ->
                                                Just ty

                                            SB.ExpTypeAll ty ->
                                                Just ty
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
            (\i ->
                { mod = i.name
                , alias_ = i.alias
                , exposing_ = i.exposing_ |> Maybe.map exposingOf
                }
            )
            (Parse.importsOf file)


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


addRef : String -> String -> Refs -> Refs
addRef mn x r =
    if mn == "" then
        { r | unqualified = x :: r.unqualified }

    else
        { r | qualified = ( mn, x ) :: r.qualified }


bind : String -> Refs -> Refs
bind x r =
    { r | binders = Set.insert x r.binders }


exprRefs : Src.Expr -> Refs -> Refs
exprRefs (A.At _ e) r =
    case e of
        Src.Call f a rest ->
            List.foldl exprRefs r (f :: List.map c1 (a :: rest))

        Src.Binops first rest last ->
            -- the operands in order, as the grouped chain visits them
            List.foldl exprRefs r (List.map Tuple.first (first :: rest) ++ [ last ])

        Src.Var _ x ->
            addRef "" x r

        Src.VarQual _ mn x ->
            addRef mn x r

        Src.If ( _, ( ( _, c ), ( _, t ) ) ) rest ( _, els ) ->
            exprRefs els
                (List.foldl (\( _, ( ( _, c_ ), ( _, t_ ) ) ) acc -> exprRefs t_ (exprRefs c_ acc))
                    (exprRefs t (exprRefs c r))
                    rest
                )

        Src.Negate a ->
            exprRefs a r

        Src.Tuple ( _, a ) ( _, b ) rest ->
            List.foldl exprRefs r (a :: b :: List.map c2 rest)

        Src.Parens ( _, a ) ->
            exprRefs a r

        Src.Let defs _ body ->
            exprRefs body
                (List.foldl
                    (\( _, A.At _ d ) acc ->
                        case d of
                            Src.Define (A.At _ name) args ( _, b ) tipe ->
                                functionRefs { name = name, args = List.map c1 args, body = b, annotation = Maybe.map (c1 >> c2) tipe } acc

                            Src.Destruct p ( _, x ) ->
                                exprRefs x (patRefs p acc)
                    )
                    r
                    defs
                )

        Src.Case ( _, x ) branches ->
            List.foldl (\( ( _, p ), ( _, b ) ) acc -> exprRefs b (patRefs p acc)) (exprRefs x r) branches

        Src.Lambda ( _, args ) ( _, b ) ->
            exprRefs b (List.foldl (c1 >> patRefs) r args)

        Src.Record ( _, setters ) ->
            List.foldl (\( _, ( _, ( _, x ) ) ) acc -> exprRefs x acc) r setters

        Src.List items _ ->
            List.foldl (c2eol >> exprRefs) r items

        Src.Access a _ ->
            exprRefs a r

        Src.Update ( _, A.At _ record ) ( _, ( first, rest ) ) ->
            List.foldl (\( _, ( _, ( _, v ) ) ) acc -> exprRefs v acc)
                (case record of
                    Src.Var _ x ->
                        addRef "" x r

                    _ ->
                        exprRefs (A.At A.zero record) r
                )
                (first :: rest)

        _ ->
            r


patRefs : Src.Pattern -> Refs -> Refs
patRefs (A.At _ p) r =
    case p of
        Src.PTuple ( _, a ) ( _, b ) rest ->
            List.foldl patRefs r (a :: b :: List.map c2 rest)

        Src.PRecord fields ->
            List.foldl (\(A.At _ f) acc -> bind f acc) r (Parse.recordPatternFields fields)

        Src.PCons ( _, a ) ( _, b ) ->
            patRefs b (patRefs a r)

        Src.PList ( _, ps ) ->
            List.foldl (c2 >> patRefs) r ps

        Src.PVar x ->
            bind x r

        Src.PCtor _ k args ->
            List.foldl (c1 >> patRefs) (addRef "" k r) args

        Src.PCtorQual _ mn k args ->
            List.foldl (c1 >> patRefs) (addRef mn k r) args

        Src.PAlias ( _, a ) ( _, A.At _ x ) ->
            bind x (patRefs a r)

        Src.PParens ( _, a ) ->
            patRefs a r

        _ ->
            r


typeRefs : Src.Type -> Refs -> Refs
typeRefs (A.At _ t) r =
    case t of
        Src.TType _ x args ->
            List.foldl (c1 >> typeRefs) (addRef "" x r) args

        Src.TTypeQual _ mn x args ->
            List.foldl (c1 >> typeRefs) (addRef mn x r) args

        Src.TTuple ( _, a ) ( _, b ) rest ->
            List.foldl typeRefs r (a :: b :: List.map c2eol rest)

        Src.TRecord fields _ ->
            List.foldl (\( _, ( _, ( _, ft ) ) ) acc -> typeRefs ft acc) r fields

        Src.TRecordExt _ first rest _ ->
            List.foldl (\( _, ( _, ( _, ft ) ) ) acc -> typeRefs ft acc) r (first :: rest)

        Src.TLambda ( _, a ) ( _, b ) ->
            typeRefs b (typeRefs a r)

        Src.TParens ( _, a ) ->
            typeRefs a r

        _ ->
            r


functionRefs : Function -> Refs -> Refs
functionRefs f r =
    let
        withSig =
            case f.annotation of
                Just t ->
                    typeRefs t r

                Nothing ->
                    r
    in
    exprRefs f.body (List.foldl patRefs (bind f.name withSig) f.args)


moduleRefs : Parsed -> Refs
moduleRefs file =
    List.foldl
        (\d acc ->
            case d of
                Decl.Value _ (A.At _ (Src.Value v)) ->
                    functionRefs
                        { name = A.toValue (c1 v.name)
                        , args = List.map c1 v.args
                        , body = c1 v.body
                        , annotation = Maybe.map (c1 >> c2) v.tipe
                        }
                        acc

                Decl.Alias _ (A.At _ (Src.Alias a)) ->
                    typeRefs (c1 a.tipe) (bind (A.toValue (c2 a.name)) acc)

                Decl.Union _ (A.At _ (Src.Union ( _, A.At _ name ) _ first rest)) ->
                    List.foldl
                        (\( _, ( A.At _ k, args ) ) acc2 -> List.foldl (c1 >> typeRefs) (bind k acc2) args)
                        (bind name acc)
                        (first :: rest)

                Decl.Port _ (Src.Port _ ( _, A.At _ name ) t) ->
                    typeRefs t (bind name acc)
        )
        emptyRefs
        (Parse.declarations file)


exposes : Exposing -> String -> Bool
exposes ex x =
    case ex of
        All ->
            True

        Explicit names ->
            List.member x names


exposesExplicitly : Exposing -> String -> Bool
exposesExplicitly ex x =
    case ex of
        All ->
            False

        Explicit _ ->
            exposes ex x


{-| What one module needs: `harness`, `library:M.x`, `outside:M` (helpers are added by the caller).
-}
moduleNeeds : SB.Basis -> Set String -> Parsed -> List String
moduleNeeds basis helpers file =
    let
        imps =
            importsOf basis.defaultImports file

        inME0 m =
            interfaceNames basis m /= Nothing

        outside =
            Parse.importsOf file
                |> List.map .name
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
        All ->
            True

        _ ->
            False


{-| The shape of `main` in the main module: "view" (an application spine of `text`), "program"
(of `Platform.worker`), or "other"; and whether it is annotated.
-}
mainShape : Parsed -> ( String, Bool )
mainShape file =
    Parse.functions file
        |> List.filter (\f -> f.name == "main")
        |> List.map (\f -> ( shapeOf f.body, f.annotation /= Nothing ))
        |> List.head
        |> Maybe.withDefault ( "other", False )


shapeOf : Src.Expr -> String
shapeOf (A.At _ e) =
    case e of
        Src.Call h _ _ ->
            shapeOf h

        Src.Parens ( _, a ) ->
            shapeOf a

        Src.Binops first rest last ->
            shapeOfChain (Fixity.tree first rest last)

        Src.Var _ x ->
            shapeOfName "" x

        Src.VarQual _ mn x ->
            shapeOfName mn x

        _ ->
            "other"


shapeOfChain : Fixity.Tree -> String
shapeOfChain t =
    case t of
        Fixity.Operand x ->
            shapeOf x

        Fixity.Apply a ->
            if a.op == "<|" then
                shapeOfChain a.left

            else if a.op == "|>" then
                shapeOfChain a.right

            else
                "other"


shapeOfName : String -> String -> String
shapeOfName mn x =
    if x == "text" && (mn == "" || mn == "Html") then
        "view"

    else if x == "worker" && (mn == "Platform" || mn == "") then
        "program"

    else
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
