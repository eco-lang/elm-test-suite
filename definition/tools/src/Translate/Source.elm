module Translate.Source exposing (Problem, annotations, program)

{-| The source syntax of a program in Lean (plans/lean-full-definition/step-08-source-syntax.md,
"Translator changes"): the elm-syntax tree mapped directly, with no inference and no
specialisation, so that compile-error tests are written too. Integer and float constants are read
from the source text (elm-syntax holds them as JavaScript numbers); a character Lean cannot hold (a
lone surrogate) and the forms outside the book's grammar are refused with a reason.
-}

import Elm.Syntax.Declaration exposing (Declaration(..))
import Elm.Syntax.Exposing exposing (Exposing(..), TopLevelExpose(..))
import Elm.Syntax.Expression exposing (Expression(..), Function, LetDeclaration(..))
import Elm.Syntax.File exposing (File)
import Elm.Syntax.Import
import Elm.Syntax.Module as M
import Elm.Syntax.Node as Node exposing (Node(..))
import Elm.Syntax.Pattern exposing (Pattern(..))
import Elm.Syntax.Range exposing (Range)
import Elm.Syntax.TypeAnnotation exposing (TypeAnnotation(..))
import Translate.Literal as Literal


type alias Problem =
    { reason : String, at : String }


type alias Ctx =
    { path : String, source : String }


type alias R a =
    Result Problem a


fail : Ctx -> Range -> String -> R a
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


isSurrogate : Char -> Bool
isSurrogate c =
    let
        n =
            Char.toCode c
    in
    -- a lone surrogate reaches Elm's Char.toCode as NaN, which no comparison holds of
    not (n >= 0 && n <= 0x0010FFFF) || (n >= 0xD800 && n <= 0xDFFF)


{-| The Lean text of a program: its modules (helpers first, the test last), wrapped in
`Src.canonOrder`.
-}
program : { project : String, name : String, defName : String } -> List { path : String, source : String, file : File } -> R String
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


moduleText : Ctx -> File -> R String
moduleText ctx file =
    let
        header =
            case Node.value file.moduleDefinition of
                M.NormalModule d ->
                    Ok ( False, d.moduleName, d.exposingList )

                M.PortModule d ->
                    Ok ( True, d.moduleName, d.exposingList )

                M.EffectModule _ ->
                    fail ctx (Node.range file.moduleDefinition) "source:effect-module"
    in
    header
        |> Result.andThen
            (\( isPort, Node _ name, Node _ ex ) ->
                Result.map2
                    (\imps decls ->
                        "Src.mdl (Src.hdr "
                            ++ (if isPort then
                                    "true"

                                else
                                    "false"
                               )
                            ++ " "
                            ++ str (String.join "." name)
                            ++ " "
                            ++ paren (exposingText ex)
                            ++ ")\n    "
                            ++ list imps
                            ++ "\n    "
                            ++ list decls
                    )
                    (combine (List.map (importText ctx) file.imports))
                    (combine (List.map (declText ctx) file.declarations))
            )


exposingText : Exposing -> String
exposingText ex =
    case ex of
        All _ ->
            ".all"

        Explicit items ->
            ".items "
                ++ list
                    (List.map
                        (\(Node _ it) ->
                            case it of
                                InfixExpose o ->
                                    ".op " ++ str o

                                FunctionExpose x ->
                                    ".var " ++ str x

                                TypeOrAliasExpose c ->
                                    ".ty " ++ str c

                                TypeExpose et ->
                                    case et.open of
                                        Just _ ->
                                            ".tyAll " ++ str et.name

                                        Nothing ->
                                            ".ty " ++ str et.name
                        )
                        items
                    )


importText : Ctx -> Node Elm.Syntax.Import.Import -> R String
importText _ (Node _ i) =
    Ok
        ("Src.imp "
            ++ str (String.join "." (Node.value i.moduleName))
            ++ " "
            ++ (case i.moduleAlias of
                    Just (Node _ a) ->
                        paren ("some " ++ str (String.join "." a))

                    Nothing ->
                        "none"
               )
            ++ " "
            ++ (case i.exposingList of
                    Just (Node _ ex) ->
                        paren ("some " ++ paren (exposingText ex))

                    Nothing ->
                        "none"
               )
        )


declText : Ctx -> Node Declaration -> R String
declText ctx (Node range d) =
    case d of
        FunctionDeclaration f ->
            functionText ctx f |> Result.map (\r -> "Src.val " ++ str r.name ++ " " ++ r.ann ++ " " ++ r.params ++ " " ++ paren r.body)

        AliasDeclaration a ->
            tyText ctx a.typeAnnotation
                |> Result.map (\t -> ".alias " ++ str (Node.value a.name) ++ " " ++ list (List.map (Node.value >> str) a.generics) ++ " " ++ paren t)

        CustomTypeDeclaration ty ->
            ty.constructors
                |> List.map
                    (\(Node _ c) ->
                        combine (List.map (tyText ctx) c.arguments)
                            |> Result.map (\args -> paren (str (Node.value c.name) ++ ", " ++ list args))
                    )
                |> combine
                |> Result.map (\cs -> ".custom " ++ str (Node.value ty.name) ++ " " ++ list (List.map (Node.value >> str) ty.generics) ++ " " ++ list cs)

        PortDeclaration s ->
            tyText ctx s.typeAnnotation |> Result.map (\t -> ".port " ++ str (Node.value s.name) ++ " " ++ paren t)

        InfixDeclaration _ ->
            fail ctx range "source:infix-declaration"

        Destructuring p e ->
            Result.map2 (\pt et -> ".value (.pat " ++ paren pt ++ " " ++ paren et ++ ")") (patText ctx p) (expText ctx e)


{-| A function binding: its name, annotation, parameters and body.
-}
functionText : Ctx -> Function -> R { name : String, ann : String, params : String, body : String }
functionText ctx f =
    let
        impl =
            Node.value f.declaration

        ann =
            case f.signature of
                Just (Node _ s) ->
                    tyText ctx s.typeAnnotation |> Result.map (\t -> paren ("some " ++ paren t))

                Nothing ->
                    Ok "none"
    in
    Result.map3 (\a ps e -> { name = Node.value impl.name, ann = a, params = list ps, body = e })
        ann
        (combine (List.map (patText ctx) impl.arguments))
        (expText ctx impl.expression)


tyText : Ctx -> Node TypeAnnotation -> R String
tyText ctx (Node range t) =
    case t of
        GenericType a ->
            Ok ("Src.tv " ++ str a)

        Typed (Node _ ( mn, name )) args ->
            combine (List.map (tyText ctx) args)
                |> Result.map
                    (\as_ ->
                        if List.isEmpty mn then
                            "Src.tc " ++ str name ++ " " ++ list as_

                        else
                            "Src.tq " ++ str (String.join "." mn) ++ " " ++ str name ++ " " ++ list as_
                    )

        Unit ->
            Ok ".unit"

        Tupled [ one ] ->
            tyText ctx one

        Tupled ts ->
            if List.length ts == 2 || List.length ts == 3 then
                combine (List.map (tyText ctx) ts) |> Result.map (\xs -> ".tuple " ++ list xs)

            else
                fail ctx range "source:tuple-arity"

        Record fs ->
            fieldsText ctx fs |> Result.map (\xs -> ".record " ++ xs)

        GenericRecord (Node _ r) (Node _ fs) ->
            fieldsText ctx fs |> Result.map (\xs -> ".ext " ++ str r ++ " " ++ xs)

        FunctionTypeAnnotation a b ->
            Result.map2 (\x y -> ".fn " ++ paren x ++ " " ++ paren y) (tyText ctx a) (tyText ctx b)


fieldsText : Ctx -> List (Node ( Node String, Node TypeAnnotation )) -> R String
fieldsText ctx fs =
    fs
        |> List.map (\(Node _ ( Node _ l, t )) -> tyText ctx t |> Result.map (\x -> paren (str l ++ ", " ++ x)))
        |> combine
        |> Result.map list


{-| The annotations of the named top-level values of a module, as a Lean list of pairs of a name
and a type expression of the source syntax (the library values of the test basis, plan step 9).
A value without an annotation is an error.
-}
annotations : { path : String, source : String } -> File -> List String -> R String
annotations ctx file names =
    let
        sigs =
            file.declarations
                |> List.filterMap
                    (\(Node _ d) ->
                        case d of
                            FunctionDeclaration f ->
                                f.signature |> Maybe.map (\(Node _ sig) -> ( Node.value sig.name, sig.typeAnnotation ))

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
intText : Ctx -> Range -> R String
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


floatText : Ctx -> Range -> R String
floatText ctx range =
    case Literal.floatOf (Literal.textAt ctx.source range |> String.trim) of
        Just f ->
            Ok (f.mantissa ++ " " ++ paren (String.fromInt f.exponent))

        Nothing ->
            fail ctx range "source:float"


charText : Ctx -> Range -> Char -> R String
charText ctx range c =
    if isSurrogate c then
        fail ctx range "source:surrogate"

    else
        Ok (Literal.leanChar c)


stringText : Ctx -> Range -> String -> R String
stringText ctx range s =
    if List.any isSurrogate (String.toList s) then
        fail ctx range "source:surrogate"

    else
        Ok (str s)


patText : Ctx -> Node Pattern -> R String
patText ctx (Node range p) =
    case p of
        AllPattern ->
            Ok ".wild"

        UnitPattern ->
            Ok ".unit"

        CharPattern c ->
            charText ctx range c |> Result.map (\x -> ".lit (.char " ++ x ++ ")")

        StringPattern s ->
            stringText ctx range s |> Result.map (\x -> ".lit (.str " ++ x ++ ")")

        IntPattern _ ->
            intText ctx range |> Result.map (\n -> ".lit (.int " ++ n ++ ")")

        HexPattern _ ->
            intText ctx range |> Result.map (\n -> ".lit (.int " ++ n ++ ")")

        FloatPattern _ ->
            floatText ctx range |> Result.map (\x -> ".lit (.float " ++ x ++ ")")

        TuplePattern ps ->
            if List.length ps == 2 || List.length ps == 3 then
                combine (List.map (patText ctx) ps) |> Result.map (\xs -> ".tuple " ++ list xs)

            else
                fail ctx range "source:tuple-arity"

        RecordPattern fs ->
            Ok (".record " ++ list (List.map (Node.value >> str) fs))

        UnConsPattern a b ->
            Result.map2 (\x y -> ".cons " ++ paren x ++ " " ++ paren y) (patText ctx a) (patText ctx b)

        ListPattern ps ->
            combine (List.map (patText ctx) ps) |> Result.map (\xs -> ".list " ++ list xs)

        VarPattern x ->
            Ok ("Src.pv " ++ str x)

        NamedPattern q args ->
            combine (List.map (patText ctx) args)
                |> Result.map
                    (\xs ->
                        if List.isEmpty q.moduleName then
                            "Src.pc " ++ str q.name ++ " " ++ list xs

                        else
                            "Src.pqc " ++ str (String.join "." q.moduleName) ++ " " ++ str q.name ++ " " ++ list xs
                    )

        AsPattern a (Node _ x) ->
            patText ctx a |> Result.map (\y -> ".as " ++ paren y ++ " " ++ str x)

        ParenthesizedPattern a ->
            patText ctx a |> Result.map (\y -> ".paren " ++ paren y)


expText : Ctx -> Node Expression -> R String
expText ctx (Node range e) =
    let
        sub =
            expText ctx
    in
    case e of
        UnitExpr ->
            Ok ".unit"

        Application (f :: args) ->
            if List.isEmpty args then
                sub f

            else
                Result.map2 (\x ys -> "Src.app " ++ paren x ++ " " ++ list ys) (sub f) (combine (List.map sub args))

        Application [] ->
            fail ctx range "source:empty-application"

        OperatorApplication o _ l r ->
            Result.map2 (\x y -> "Src.bin " ++ str o ++ " " ++ paren x ++ " " ++ paren y) (sub l) (sub r)

        FunctionOrValue mn x ->
            let
                upper =
                    String.left 1 x /= String.toLower (String.left 1 x)
            in
            Ok
                (case ( List.isEmpty mn, upper ) of
                    ( True, True ) ->
                        "Src.c " ++ str x

                    ( True, False ) ->
                        "Src.v " ++ str x

                    ( False, True ) ->
                        "Src.qc " ++ str (String.join "." mn) ++ " " ++ str x

                    ( False, False ) ->
                        "Src.qv " ++ str (String.join "." mn) ++ " " ++ str x
                )

        IfBlock c t f ->
            ifChain ctx [ ( c, t ) ] f

        PrefixOperator o ->
            Ok (".opVal " ++ str o)

        Operator o ->
            Ok (".opVal " ++ str o)

        Integer _ ->
            intText ctx range |> Result.map (\n -> "Src.i " ++ n)

        Hex _ ->
            intText ctx range |> Result.map (\n -> "Src.i " ++ n)

        Floatable _ ->
            floatText ctx range |> Result.map (\x -> "Src.fl " ++ x)

        Negation a ->
            sub a |> Result.map (\x -> ".neg " ++ paren x)

        Literal s ->
            stringText ctx range s |> Result.map (\x -> "Src.str " ++ x)

        CharLiteral c ->
            charText ctx range c |> Result.map (\x -> "Src.ch " ++ x)

        TupledExpression es ->
            if List.length es == 2 || List.length es == 3 then
                combine (List.map sub es) |> Result.map (\xs -> ".tuple " ++ list xs)

            else
                fail ctx range "source:tuple-arity"

        ParenthesizedExpression a ->
            sub a |> Result.map (\x -> ".paren " ++ paren x)

        LetExpression lb ->
            Result.map2 (\ds b -> ".letE " ++ list ds ++ " " ++ paren b)
                (combine
                    (List.map
                        (\(Node _ d) ->
                            case d of
                                LetFunction f ->
                                    functionText ctx f |> Result.map (\r -> ".fn " ++ str r.name ++ " " ++ r.ann ++ " " ++ r.params ++ " " ++ paren r.body)

                                LetDestructuring p x ->
                                    Result.map2 (\pt xt -> ".pat " ++ paren pt ++ " " ++ paren xt) (patText ctx p) (sub x)
                        )
                        lb.declarations
                    )
                )
                (sub lb.expression)

        CaseExpression cb ->
            Result.map2 (\x rs -> ".caseE " ++ paren x ++ " " ++ list rs)
                (sub cb.expression)
                (combine (List.map (\( p, x ) -> Result.map2 (\pt xt -> paren (pt ++ ", " ++ xt)) (patText ctx p) (sub x)) cb.cases))

        LambdaExpression l ->
            Result.map2 (\ps b -> ".lam " ++ list ps ++ " " ++ paren b) (combine (List.map (patText ctx) l.args)) (sub l.expression)

        RecordExpr setters ->
            setterText ctx setters |> Result.map (\fs -> ".record " ++ fs)

        ListExpr es ->
            combine (List.map sub es) |> Result.map (\xs -> ".list " ++ list xs)

        RecordAccess a (Node _ l) ->
            sub a |> Result.map (\x -> ".access " ++ paren x ++ " " ++ str l)

        RecordAccessFunction l ->
            Ok (".accessor " ++ str (String.dropLeft 1 l))

        RecordUpdateExpression (Node _ x) setters ->
            setterText ctx setters |> Result.map (\fs -> ".update " ++ str x ++ " " ++ fs)

        GLSLExpression _ ->
            fail ctx range "source:glsl"


setterText : Ctx -> List (Node ( Node String, Node Expression )) -> R String
setterText ctx setters =
    setters
        |> List.map (\(Node _ ( Node _ l, x )) -> expText ctx x |> Result.map (\y -> paren (str l ++ ", " ++ y)))
        |> combine
        |> Result.map list


{-| The maximal chain of unparenthesised `if`s in else-branches.
-}
ifChain : Ctx -> List ( Node Expression, Node Expression ) -> Node Expression -> R String
ifChain ctx arms els =
    case Node.value els of
        IfBlock c t f ->
            ifChain ctx (arms ++ [ ( c, t ) ]) f

        _ ->
            Result.map2 (\as_ e -> ".ifte " ++ list as_ ++ " " ++ paren e)
                (combine (List.map (\( c, t ) -> Result.map2 (\x y -> paren (x ++ ", " ++ y)) (expText ctx c) (expText ctx t)) arms))
                (expText ctx els)
