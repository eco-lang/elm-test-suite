module Translate.FrontEnd exposing (Refusal, check, escapeProblem)

{-| The restrictions of the concrete syntax that eco's tree lets the translator see, and that stay
outside Lean (plans/eco-parser.md, E6): checked on every module of a program after it parses and
before anything reads its tree (E7).

| Reason | What is refused |
| ----------------------------- | ---------------------------------------------------------------------- |
| `syntax:core-operator-chain` | an operator chain `res:core-operator-chain` forbids (`Fixity`) |
| `syntax:operator` | an operator outside `fig:core-fixities` |
| `syntax:tuple-arity` | a tuple expression, pattern or type of more than three components |
| `syntax:core-adjacent-items` | a unit pattern `( )` with a gap: its region not two columns wide |
| `syntax:core-escape-unicode` | an escape `\u{h}` naming a surrogate (D800 to DFFF) or above 10FFFF |
| `syntax:modules-header` | a module without a `module` or `port module` header |

eco's parser already rejects every other gap `res:core-adjacent-items` names (`( + )`, `x = ( )`, a
type `( )`, `M. x`, `r. x`, `- x`). An escape is read from the source text at the literal's region,
since eco holds a literal's text escaped again.

-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Compiler.Parse.Declaration as Decl
import Dict
import Translate.Fixity as Fixity
import Translate.Literal as Literal
import Translate.Parse as Parse exposing (Parsed, c1, c2, c2eol)
import Translate.Region as Region exposing (Region)


type alias Refusal =
    { reason : String, at : Region }


{-| Every refusal of a module, in source order.
-}
check : { path : String, source : String } -> Parsed -> List Refusal
check ctx parsed =
    let
        header =
            case parsed.header of
                Nothing ->
                    [ { reason = "syntax:modules-header", at = Parse.headerRegion parsed } ]

                Just _ ->
                    []
    in
    (header ++ List.concatMap (decl ctx.source) parsed.decls)
        |> List.sortBy (\r -> ( r.at.start.row, r.at.start.column ))


refuse : String -> A.Region -> List Refusal
refuse reason r =
    [ { reason = reason, at = Region.fromA r } ]


decl : String -> Decl.Decl -> List Refusal
decl src d =
    case d of
        Decl.Value _ (A.At _ (Src.Value v)) ->
            List.concatMap (c1 >> pat src) v.args
                ++ (v.tipe |> Maybe.map (c1 >> c2 >> typ) |> Maybe.withDefault [])
                ++ expr src (c1 v.body)

        Decl.Union _ (A.At _ (Src.Union _ _ first rest)) ->
            List.concatMap (\( _, ( _, ts ) ) -> List.concatMap (c1 >> typ) ts) (first :: rest)

        Decl.Alias _ (A.At _ (Src.Alias a)) ->
            typ (c1 a.tipe)

        Decl.Port _ (Src.Port _ _ t) ->
            typ t


expr : String -> Src.Expr -> List Refusal
expr src (A.At region e) =
    let
        ex =
            expr src
    in
    case e of
        Src.Chr _ ->
            escapes src region

        Src.Str _ _ ->
            escapes src region

        Src.Int _ _ ->
            []

        Src.Float _ _ ->
            []

        Src.Var _ _ ->
            []

        Src.VarQual _ _ _ ->
            []

        Src.List items _ ->
            List.concatMap (c2eol >> ex) items

        Src.Op o ->
            if Dict.member o Fixity.table then
                []

            else
                refuse "syntax:operator" region

        Src.Negate x ->
            ex x

        Src.Binops first rest last ->
            (case Fixity.check first rest last of
                Just r ->
                    [ r ]

                Nothing ->
                    []
            )
                ++ List.concatMap (Tuple.first >> ex) (first :: rest)
                ++ ex last

        Src.Lambda ( _, ps ) ( _, b ) ->
            List.concatMap (c1 >> pat src) ps ++ ex b

        Src.Call f a rest ->
            ex f ++ List.concatMap (c1 >> ex) (a :: rest)

        Src.If ( _, ( ( _, c ), ( _, t ) ) ) rest ( _, el ) ->
            ex c ++ ex t ++ List.concatMap (\( _, ( ( _, c_ ), ( _, t_ ) ) ) -> ex c_ ++ ex t_) rest ++ ex el

        Src.Let defs _ body ->
            List.concatMap
                (\( _, A.At _ def ) ->
                    case def of
                        Src.Define _ ps ( _, b ) tipe ->
                            List.concatMap (c1 >> pat src) ps
                                ++ (tipe |> Maybe.map (c1 >> c2 >> typ) |> Maybe.withDefault [])
                                ++ ex b

                        Src.Destruct p ( _, b ) ->
                            pat src p ++ ex b
                )
                defs
                ++ ex body

        Src.Case ( _, x ) branches ->
            ex x ++ List.concatMap (\( ( _, p ), ( _, b ) ) -> pat src p ++ ex b) branches

        Src.Accessor _ ->
            []

        Src.Access x _ ->
            ex x

        Src.Update ( _, x ) ( _, ( f1, fs ) ) ->
            ex x ++ List.concatMap (\( _, ( _, ( _, v ) ) ) -> ex v) (f1 :: fs)

        Src.Record ( _, fs ) ->
            List.concatMap (\( _, ( _, ( _, v ) ) ) -> ex v) fs

        Src.Unit ->
            []

        Src.Tuple ( _, a ) ( _, b ) rest ->
            (if List.length rest > 1 then
                refuse "syntax:tuple-arity" region

             else
                []
            )
                ++ ex a
                ++ ex b
                ++ List.concatMap (c2 >> ex) rest

        Src.Parens ( _, x ) ->
            ex x


pat : String -> Src.Pattern -> List Refusal
pat src (A.At region p) =
    let
        pt =
            pat src
    in
    case p of
        Src.PAnything _ ->
            []

        Src.PVar _ ->
            []

        Src.PRecord _ ->
            []

        Src.PAlias ( _, x ) _ ->
            pt x

        Src.PUnit _ ->
            let
                r =
                    Region.fromA region
            in
            if r.start.row /= r.end.row || r.end.column - r.start.column /= 2 then
                refuse "syntax:core-adjacent-items" region

            else
                []

        Src.PTuple ( _, a ) ( _, b ) rest ->
            (if List.length rest > 1 then
                refuse "syntax:tuple-arity" region

             else
                []
            )
                ++ pt a
                ++ pt b
                ++ List.concatMap (c2 >> pt) rest

        Src.PCtor _ _ args ->
            List.concatMap (c1 >> pt) args

        Src.PCtorQual _ _ _ args ->
            List.concatMap (c1 >> pt) args

        Src.PList ( _, xs ) ->
            List.concatMap (c2 >> pt) xs

        Src.PCons ( _, a ) ( _, b ) ->
            pt a ++ pt b

        Src.PChr _ ->
            escapes src region

        Src.PStr _ _ ->
            escapes src region

        Src.PInt _ _ ->
            []

        Src.PParens ( _, x ) ->
            pt x


typ : Src.Type -> List Refusal
typ (A.At region t) =
    case t of
        Src.TLambda ( _, a ) ( _, b ) ->
            typ a ++ typ b

        Src.TVar _ ->
            []

        Src.TType _ _ args ->
            List.concatMap (c1 >> typ) args

        Src.TTypeQual _ _ _ args ->
            List.concatMap (c1 >> typ) args

        Src.TRecord fs _ ->
            List.concatMap (\( _, ( _, ( _, x ) ) ) -> typ x) fs

        Src.TRecordExt _ f1 fs _ ->
            List.concatMap (\( _, ( _, ( _, x ) ) ) -> typ x) (f1 :: fs)

        Src.TUnit ->
            []

        Src.TTuple ( _, a ) ( _, b ) rest ->
            (if List.length rest > 1 then
                refuse "syntax:tuple-arity" region

             else
                []
            )
                ++ typ a
                ++ typ b
                ++ List.concatMap (c2eol >> typ) rest

        Src.TParens ( _, x ) ->
            typ x


escapes : String -> A.Region -> List Refusal
escapes src region =
    if escapeProblem (Literal.textAt src (Region.fromA region)) then
        refuse "syntax:core-escape-unicode" region

    else
        []


{-| Whether the text of a character or string literal has an escape `\u{h}` whose value is a
surrogate (D800 to DFFF) or above 10FFFF. Every other escape is stepped over as a pair, so that
`"\\u{D800}"` (an escaped backslash, then text) is not one.
-}
escapeProblem : String -> Bool
escapeProblem text =
    scan (String.toList text)


scan : List Char -> Bool
scan chars =
    case chars of
        '\\' :: 'u' :: '{' :: rest ->
            let
                digits =
                    takeHex rest

                value =
                    List.foldl (\c acc -> acc * 16 + hexValue c) 0 digits
            in
            if (value >= 0xD800 && value <= 0xDFFF) || value > 0x0010FFFF then
                True

            else
                scan (List.drop (List.length digits) rest)

        '\\' :: _ :: rest ->
            scan rest

        _ :: rest ->
            scan rest

        [] ->
            False


takeHex : List Char -> List Char
takeHex chars =
    case chars of
        c :: rest ->
            if Char.isHexDigit c then
                c :: takeHex rest

            else
                []

        [] ->
            []


hexValue : Char -> Int
hexValue c =
    let
        n =
            Char.toCode (Char.toUpper c)
    in
    if n <= 0x39 then
        n - 0x30

    else
        n - 0x37
