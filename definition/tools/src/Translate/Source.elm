module Translate.Source exposing (Problem, annotations, program)

{-| The source syntax of a program in Lean (plans/lean-full-definition/step-08-source-syntax.md,
"Translator changes"): eco's tree mapped directly, operator chains grouped by the book's fixities
(`Translate.Fixity`), with no inference and no specialisation, so that compile-error tests are
written too. Integer and float constants are read from the source text (eco holds them as
JavaScript numbers beside their text). The front end (`Translate.FrontEnd`) has already refused the
forms outside the book's grammar and the escapes Lean cannot hold.
-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Compiler.Parse.Declaration as Decl
import Translate.Fixity as Fixity
import Translate.Literal as Literal
import Translate.Parse as Parse exposing (Parsed, c1, c2, c2eol)
import Translate.Region as Region exposing (Region)


type alias Problem =
    { reason : String, at : String }


type alias Ctx =
    { path : String, source : String }


type alias R a =
    Result Problem a


fail : Ctx -> Region -> String -> R a
fail ctx range reason =
    Err { reason = reason, at = ctx.path ++ ":" ++ String.fromInt range.start.row ++ ":" ++ String.fromInt range.start.column }


combine : List (R a) -> R (List a)
combine =
    List.foldr (Result.map2 (::)) (Ok [])


list : List String -> String
list items =
    "[" ++ String.join ", " items ++ "]"


paren : String -> String
paren s =
    "(" ++ s ++ ")"


str : String -> String
str =
    Literal.leanString


{-| The Lean text of a program: its modules (helpers first, the test last), wrapped in
`Src.canonOrder`.
-}
program : { project : String, name : String, defName : String } -> List { path : String, source : String, file : Parsed } -> R String
program info modules =
    modules
        |> List.map (\m -> moduleText { path = m.path, source = m.source } m.file)
        |> combine
        |> Result.map
            (\ms ->
                "/-- "
                    ++ String.join ", " (List.map .path modules)
                    ++ " -/\ndef "
                    ++ info.defName
                    ++ " : Src.SProgram := Src.canonOrder <| Src.prog "
                    ++ str info.project
                    ++ " "
                    ++ str info.name
                    ++ " [\n  "
                    ++ String.join ",\n  " ms
                    ++ " ]"
            )


moduleText : Ctx -> Parsed -> R String
moduleText ctx file =
    case file.infixes of
        (A.At r _) :: _ ->
            fail ctx (Region.fromA r) "source:infix-declaration"

        [] ->
            moduleBody ctx file


moduleBody : Ctx -> Parsed -> R String
moduleBody ctx file =
    Result.map2
        (\imps decls ->
            "Src.mdl (Src.hdr "
                ++ (if Parse.isPortModule file then
                        "true"

                    else
                        "false"
                   )
                ++ " "
                ++ str (Parse.moduleName file |> Maybe.withDefault "Main")
                ++ " "
                ++ paren (exposingText (Parse.exposing_ file))
                ++ ")\n    "
                ++ list imps
                ++ "\n    "
                ++ list decls
        )
        (combine (List.map importText (Parse.importsOf file)))
        (combine (List.map (declText ctx) (Parse.declarations file)))


exposingText : Src.Exposing -> String
exposingText ex =
    case ex of
        Src.Open _ _ ->
            ".all"

        Src.Explicit (A.At _ items) ->
            ".items "
                ++ list
                    (List.map
                        (\( _, it ) ->
                            case it of
                                Src.Operator _ o ->
                                    ".op " ++ str o

                                Src.Lower (A.At _ x) ->
                                    ".var " ++ str x

                                Src.Upper (A.At _ c) ( _, Src.Private ) ->
                                    ".ty " ++ str c

                                Src.Upper (A.At _ c) ( _, Src.Public _ ) ->
                                    ".tyAll " ++ str c
                        )
                        items
                    )


importText : Parse.Import -> R String
importText i =
    Ok
        ("Src.imp "
            ++ str i.name
            ++ " "
            ++ (case i.alias of
                    Just a ->
                        paren ("some " ++ str a)

                    Nothing ->
                        "none"
               )
            ++ " "
            ++ (case i.exposing_ of
                    Just ex ->
                        paren ("some " ++ paren (exposingText ex))

                    Nothing ->
                        "none"
               )
        )


declText : Ctx -> Decl.Decl -> R String
declText ctx d =
    case d of
        Decl.Value _ (A.At _ (Src.Value v)) ->
            functionText ctx
                { name = A.toValue (c1 v.name)
                , args = List.map c1 v.args
                , body = c1 v.body
                , annotation = Maybe.map (c1 >> c2) v.tipe
                }
                |> Result.map (\r -> "Src.val " ++ str r.name ++ " " ++ r.ann ++ " " ++ r.params ++ " " ++ paren r.body)

        Decl.Alias _ (A.At _ (Src.Alias a)) ->
            tyText ctx (c1 a.tipe)
                |> Result.map (\t -> ".alias " ++ str (A.toValue (c2 a.name)) ++ " " ++ list (List.map (c1 >> A.toValue >> str) a.args) ++ " " ++ paren t)

        Decl.Union _ (A.At _ (Src.Union ( _, A.At _ name ) params first rest)) ->
            (first :: rest)
                |> List.map
                    (\( _, ( A.At _ k, args ) ) ->
                        combine (List.map (c1 >> tyText ctx) args)
                            |> Result.map (\xs -> paren (str k ++ ", " ++ list xs))
                    )
                |> combine
                |> Result.map (\cs -> ".custom " ++ str name ++ " " ++ list (List.map (c1 >> A.toValue >> str) params) ++ " " ++ list cs)

        Decl.Port _ (Src.Port _ ( _, A.At _ name ) t) ->
            tyText ctx t |> Result.map (\x -> ".port " ++ str name ++ " " ++ paren x)


{-| A function binding: its name, annotation, parameters and body.
-}
functionText : Ctx -> { name : String, args : List Src.Pattern, body : Src.Expr, annotation : Maybe Src.Type } -> R { name : String, ann : String, params : String, body : String }
functionText ctx f =
    let
        ann =
            case f.annotation of
                Just t ->
                    tyText ctx t |> Result.map (\x -> paren ("some " ++ paren x))

                Nothing ->
                    Ok "none"
    in
    Result.map3 (\a ps e -> { name = f.name, ann = a, params = list ps, body = e })
        ann
        (combine (List.map (patText ctx) f.args))
        (expText ctx f.body)


tyText : Ctx -> Src.Type -> R String
tyText ctx (A.At _ t) =
    case t of
        Src.TVar a ->
            Ok ("Src.tv " ++ str a)

        Src.TType _ name args ->
            combine (List.map (c1 >> tyText ctx) args)
                |> Result.map (\as_ -> "Src.tc " ++ str name ++ " " ++ list as_)

        Src.TTypeQual _ mn name args ->
            combine (List.map (c1 >> tyText ctx) args)
                |> Result.map (\as_ -> "Src.tq " ++ str mn ++ " " ++ str name ++ " " ++ list as_)

        Src.TUnit ->
            Ok ".unit"

        Src.TParens ( _, inner ) ->
            tyText ctx inner

        Src.TTuple ( _, a ) ( _, b ) rest ->
            combine (List.map (tyText ctx) (a :: b :: List.map c2eol rest)) |> Result.map (\xs -> ".tuple " ++ list xs)

        Src.TRecord fs _ ->
            fieldsText ctx fs |> Result.map (\xs -> ".record " ++ xs)

        Src.TRecordExt ( _, A.At _ r ) first rest _ ->
            fieldsText ctx (first :: rest) |> Result.map (\xs -> ".ext " ++ str r ++ " " ++ xs)

        Src.TLambda ( _, a ) ( _, b ) ->
            Result.map2 (\x y -> ".fn " ++ paren x ++ " " ++ paren y) (tyText ctx a) (tyText ctx b)


fieldsText : Ctx -> List (Src.C2 ( Src.C1 (A.Located String), Src.C1 Src.Type )) -> R String
fieldsText ctx fs =
    fs
        |> List.map (\( _, ( ( _, A.At _ l ), ( _, t ) ) ) -> tyText ctx t |> Result.map (\x -> paren (str l ++ ", " ++ x)))
        |> combine
        |> Result.map list


{-| The annotations of the named top-level values of a module, as a Lean list of pairs of a name
and a type expression of the source syntax (the library values of the test basis, plan step 9).
A value without an annotation is an error.
-}
annotations : { path : String, source : String } -> Parsed -> List String -> R String
annotations ctx file names =
    let
        sigs =
            Parse.declarations file
                |> List.filterMap
                    (\d ->
                        case d of
                            Decl.Value _ (A.At _ (Src.Value v)) ->
                                v.tipe |> Maybe.map (\t -> ( A.toValue (c1 v.name), c2 (c1 t) ))

                            _ ->
                                Nothing
                    )
    in
    names
        |> List.map
            (\n ->
                case List.filter (\( m, _ ) -> m == n) sigs |> List.head of
                    Just ( _, t ) ->
                        tyText ctx t |> Result.map (\x -> paren (str n ++ ", " ++ x))

                    Nothing ->
                        Err { reason = "library:no-annotation:" ++ n, at = ctx.path }
            )
        |> combine
        |> Result.map list


{-| An integer constant from its text: decimal or hexadecimal, exactly.
-}
intText : Ctx -> Region -> R String
intText ctx range =
    let
        text =
            Literal.textAt ctx.source range |> String.trim
    in
    if String.startsWith "-" text then
        fail ctx range "source:negative-pattern"

    else if String.startsWith "0x" text || String.startsWith "0X" text then
        Ok (Literal.decimalOfHex text)

    else
        Ok (Literal.normaliseDecimal text)


floatText : Ctx -> Region -> R String
floatText ctx range =
    case Literal.floatOf (Literal.textAt ctx.source range |> String.trim) of
        Just f ->
            Ok (f.mantissa ++ " " ++ paren (String.fromInt f.exponent))

        Nothing ->
            fail ctx range "source:float"


patText : Ctx -> Src.Pattern -> R String
patText ctx (A.At region p) =
    let
        range =
            Region.fromA region
    in
    case p of
        Src.PAnything _ ->
            Ok ".wild"

        Src.PUnit _ ->
            Ok ".unit"

        Src.PChr text ->
            Ok (".lit (.char " ++ Literal.leanChar (Parse.charValue text) ++ ")")

        Src.PStr text _ ->
            Ok (".lit (.str " ++ str (Parse.stringValue text) ++ ")")

        Src.PInt _ _ ->
            intText ctx range |> Result.map (\n -> ".lit (.int " ++ n ++ ")")

        Src.PTuple ( _, a ) ( _, b ) rest ->
            combine (List.map (patText ctx) (a :: b :: List.map c2 rest)) |> Result.map (\xs -> ".tuple " ++ list xs)

        Src.PRecord fields ->
            Ok (".record " ++ list (List.map (A.toValue >> str) (Parse.recordPatternFields fields)))

        Src.PCons ( _, a ) ( _, b ) ->
            Result.map2 (\x y -> ".cons " ++ paren x ++ " " ++ paren y) (patText ctx a) (patText ctx b)

        Src.PList ( _, ps ) ->
            combine (List.map (c2 >> patText ctx) ps) |> Result.map (\xs -> ".list " ++ list xs)

        Src.PVar x ->
            Ok ("Src.pv " ++ str x)

        Src.PCtor _ k args ->
            combine (List.map (c1 >> patText ctx) args)
                |> Result.map (\xs -> "Src.pc " ++ str k ++ " " ++ list xs)

        Src.PCtorQual _ q k args ->
            combine (List.map (c1 >> patText ctx) args)
                |> Result.map (\xs -> "Src.pqc " ++ str q ++ " " ++ str k ++ " " ++ list xs)

        Src.PAlias ( _, a ) ( _, A.At _ x ) ->
            patText ctx a |> Result.map (\y -> ".as " ++ paren y ++ " " ++ str x)

        Src.PParens ( _, a ) ->
            patText ctx a |> Result.map (\y -> ".paren " ++ paren y)


expText : Ctx -> Src.Expr -> R String
expText ctx (A.At region e) =
    let
        sub =
            expText ctx

        range =
            Region.fromA region
    in
    case e of
        Src.Unit ->
            Ok ".unit"

        Src.Call f a rest ->
            Result.map2 (\x ys -> "Src.app " ++ paren x ++ " " ++ list ys) (sub f) (combine (List.map (c1 >> sub) (a :: rest)))

        Src.Binops first rest last ->
            chainText ctx (Fixity.tree first rest last)

        Src.Var _ x ->
            Ok (varText "" x)

        Src.VarQual _ mn x ->
            Ok (varText mn x)

        Src.If ( _, ( ( _, c ), ( _, t ) ) ) rest ( _, els ) ->
            Result.map2 (\as_ x -> ".ifte " ++ list as_ ++ " " ++ paren x)
                (combine
                    (List.map (\( c_, t_ ) -> Result.map2 (\x y -> paren (x ++ ", " ++ y)) (sub c_) (sub t_))
                        (( c, t ) :: List.map (\( _, ( ( _, c_ ), ( _, t_ ) ) ) -> ( c_, t_ )) rest)
                    )
                )
                (sub els)

        Src.Op o ->
            Ok (".opVal " ++ str o)

        Src.Int _ _ ->
            intText ctx range |> Result.map (\n -> "Src.i " ++ n)

        Src.Float _ _ ->
            floatText ctx range |> Result.map (\x -> "Src.fl " ++ x)

        Src.Negate a ->
            sub a |> Result.map (\x -> ".neg " ++ paren x)

        Src.Str text _ ->
            Ok ("Src.str " ++ str (Parse.stringValue text))

        Src.Chr text ->
            Ok ("Src.ch " ++ Literal.leanChar (Parse.charValue text))

        Src.Tuple ( _, a ) ( _, b ) rest ->
            combine (List.map sub (a :: b :: List.map c2 rest)) |> Result.map (\xs -> ".tuple " ++ list xs)

        Src.Parens ( _, a ) ->
            sub a |> Result.map (\x -> ".paren " ++ paren x)

        Src.Let defs _ body ->
            Result.map2 (\ds b -> ".letE " ++ list ds ++ " " ++ paren b)
                (combine
                    (List.map
                        (\( _, A.At _ d ) ->
                            case d of
                                Src.Define (A.At _ name) args ( _, b ) tipe ->
                                    functionText ctx { name = name, args = List.map c1 args, body = b, annotation = Maybe.map (c1 >> c2) tipe }
                                        |> Result.map (\r -> ".fn " ++ str r.name ++ " " ++ r.ann ++ " " ++ r.params ++ " " ++ paren r.body)

                                Src.Destruct p ( _, x ) ->
                                    Result.map2 (\pt xt -> ".pat " ++ paren pt ++ " " ++ paren xt) (patText ctx p) (sub x)
                        )
                        defs
                    )
                )
                (sub body)

        Src.Case ( _, x ) branches ->
            Result.map2 (\xt rs -> ".caseE " ++ paren xt ++ " " ++ list rs)
                (sub x)
                (combine (List.map (\( ( _, p ), ( _, b ) ) -> Result.map2 (\pt bt -> paren (pt ++ ", " ++ bt)) (patText ctx p) (sub b)) branches))

        Src.Lambda ( _, args ) ( _, b ) ->
            Result.map2 (\ps bt -> ".lam " ++ list ps ++ " " ++ paren bt) (combine (List.map (c1 >> patText ctx) args)) (sub b)

        Src.Record ( _, setters ) ->
            setterText ctx (List.map c2eol setters) |> Result.map (\fs -> ".record " ++ fs)

        Src.List items _ ->
            combine (List.map (c2eol >> sub) items) |> Result.map (\xs -> ".list " ++ list xs)

        Src.Access a (A.At _ l) ->
            sub a |> Result.map (\x -> ".access " ++ paren x ++ " " ++ str l)

        Src.Accessor l ->
            Ok (".accessor " ++ str l)

        Src.Update ( _, A.At _ record ) ( _, ( first, rest ) ) ->
            case record of
                Src.Var _ x ->
                    setterText ctx (List.map c2eol (first :: rest)) |> Result.map (\fs -> ".update " ++ str x ++ " " ++ fs)

                _ ->
                    fail ctx range "source:record-update"


{-| A variable or constructor `mn.x` as written (`mn` "" when unqualified).
-}
varText : String -> String -> String
varText mn x =
    let
        upper =
            String.left 1 x /= String.toLower (String.left 1 x)
    in
    case ( mn == "", upper ) of
        ( True, True ) ->
            "Src.c " ++ str x

        ( True, False ) ->
            "Src.v " ++ str x

        ( False, True ) ->
            "Src.qc " ++ str mn ++ " " ++ str x

        ( False, False ) ->
            "Src.qv " ++ str mn ++ " " ++ str x


{-| An operator chain, grouped by the book's fixities.
-}
chainText : Ctx -> Fixity.Tree -> R String
chainText ctx t =
    case t of
        Fixity.Operand x ->
            expText ctx x

        Fixity.Apply a ->
            Result.map2 (\x y -> "Src.bin " ++ str a.op ++ " " ++ paren x ++ " " ++ paren y) (chainText ctx a.left) (chainText ctx a.right)


setterText : Ctx -> List ( Src.C1 (A.Located String), Src.C1 Src.Expr ) -> R String
setterText ctx setters =
    setters
        |> List.map (\( ( _, A.At _ l ), ( _, x ) ) -> expText ctx x |> Result.map (\y -> paren (str l ++ ", " ++ y)))
        |> combine
        |> Result.map list
