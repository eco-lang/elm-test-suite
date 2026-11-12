module DerivedForms.ToLean exposing (bareDefinitions, definitions, orderedRows, plain)

{-| Prints the generated rows of Appendix A as Lean definitions over the bare syntax of
`Syntax.lean`, with the names and parameters `Derived.lean` has always used.
-}

import Dict exposing (Dict)
import DerivedForms.Term exposing (..)
import DerivedForms.ToLatex as ToLatex
import Regex


type Side
    = ExpSide
    | PatSide


leanType : Meta -> String
leanType meta =
    case meta of
        Exp ->
            "Exp"

        AtExp ->
            "AtExp"

        Pat ->
            "Pat"

        AtPat ->
            "AtPat"

        Opv ->
            "Op"

        Lab ->
            "Lab"


metaOf : Ref -> Meta
metaOf r =
    case r of
        Plain m ->
            m

        Indexed m _ ->
            m

        Item m ->
            m

        ItemPrimed m ->
            m


refKey : Ref -> String
refKey r =
    case r of
        Plain m ->
            "p" ++ leanType m

        Indexed m k ->
            "x" ++ leanType m ++ String.fromInt k

        Item m ->
            "i" ++ leanType m

        ItemPrimed m ->
            "j" ++ leanType m


type alias Ctx =
    { rows : Dict String Row
    , names : Dict String String
    , hole : Maybe ( Meta, String )
    }


paren : String -> String
paren s =
    if String.contains " " s then
        "(" ++ s ++ ")"

    else
        s


coerce : Meta -> ( Meta, String ) -> Result String String
coerce want ( have, text ) =
    if want == have then
        Ok text

    else
        case ( have, want ) of
            ( AtExp, Exp ) ->
                Ok (".atexp " ++ paren text)

            ( AtPat, Pat ) ->
                Ok (".atpat " ++ paren text)

            _ ->
                Err ("a " ++ leanType have ++ " where a " ++ leanType want ++ " is needed: " ++ text)


as_ : Ctx -> Side -> Meta -> Term -> Result String String
as_ ctx side want t =
    raw ctx side t |> Result.andThen (coerce want)


atomic : Side -> Meta
atomic side =
    case side of
        ExpSide ->
            AtExp

        PatSide ->
            AtPat


name : Ctx -> Ref -> Result String String
name ctx r =
    Dict.get (refKey r) ctx.names |> Result.fromMaybe ("no parameter for " ++ refKey r)


raw : Ctx -> Side -> Term -> Result String ( Meta, String )
raw ctx side t =
    case t of
        TMeta r ->
            name ctx r |> Result.map (\n -> ( metaOf r, n ))

        TApp f a ->
            Result.map2 (\ft at -> ( Exp, ".app " ++ paren ft ++ " " ++ paren at ))
                (as_ ctx ExpSide Exp f)
                (as_ ctx ExpSide AtExp a)

        TParen e ->
            case side of
                ExpSide ->
                    as_ ctx side Exp e |> Result.map (\et -> ( AtExp, ".paren " ++ paren et ))

                PatSide ->
                    as_ ctx side Pat e |> Result.map (\pt -> ( AtPat, ".paren " ++ paren pt ))

        TOp r ->
            name ctx r |> Result.map (\n -> ( AtExp, ".op " ++ n ))

        TOpLit s ->
            Ok ( AtExp, ".op \"" ++ s ++ "\"" )

        TVarQual m x ->
            Ok ( AtExp, ".var " ++ qualified m x )

        TConQual m x ->
            Ok ( atomic side, ".con " ++ qualified m x )

        TVarOfLab r ->
            name ctx r |> Result.map (\n -> ( AtExp, ".var ⟨none, " ++ n ++ "⟩" ))

        TLam p e ->
            Result.map2 (\pt et -> ( Exp, ".lam " ++ paren pt ++ " " ++ paren et ))
                (as_ ctx PatSide AtPat p)
                (as_ ctx ExpSide Exp e)

        TCase e rules ->
            Result.map2 (\et mt -> ( Exp, ".caseE " ++ paren et ++ " " ++ paren mt ))
                (as_ ctx ExpSide Exp e)
                (matchOf ctx rules)

        TNil ->
            Ok ( atomic side, ".nil" )

        TRecordPat1 r ->
            name ctx r |> Result.map (\n -> ( AtPat, ".record (some (.field " ++ n ++ " none))" ))

        TPatCons p q ->
            Result.map2 (\pt qt -> ( Pat, ".cons " ++ paren pt ++ " " ++ paren qt ))
                (as_ ctx PatSide Pat p)
                (as_ ctx PatSide Pat q)

        TUse label args ->
            case Dict.get label ctx.rows |> Maybe.map .lean of
                Just (Generated g) ->
                    List.map2
                        (\param arg ->
                            case ( metaOf param.ref, arg ) of
                                ( Opv, TOpLit s ) ->
                                    Ok ("\"" ++ s ++ "\"")

                                ( m, _ ) ->
                                    as_ ctx (sideOf m) m arg
                        )
                        g.params
                        args
                        |> combine
                        |> Result.map (\ts -> ( g.result, String.join " " (g.name :: List.map paren ts) ))

                _ ->
                    Err ("no generated row " ++ label)

        TNestRight _ ->
            Err "a nested sequence must be the row's sequence"

        THole ->
            ctx.hole |> Result.fromMaybe "a hole outside a sequence"


{-| The class of a term, without printing it.
-}
classOf : Dict String Row -> Side -> Term -> Meta
classOf rows side t =
    case t of
        TMeta r ->
            metaOf r

        TApp _ _ ->
            Exp

        TParen _ ->
            atomic side

        TOp _ ->
            AtExp

        TOpLit _ ->
            AtExp

        TVarQual _ _ ->
            AtExp

        TVarOfLab _ ->
            AtExp

        TConQual _ _ ->
            atomic side

        TNil ->
            atomic side

        TLam _ _ ->
            Exp

        TCase _ _ ->
            Exp

        TRecordPat1 _ ->
            AtPat

        TPatCons _ _ ->
            Pat

        TUse label _ ->
            case Dict.get label rows |> Maybe.map .lean of
                Just (Generated g) ->
                    g.result

                _ ->
                    Exp

        TNestRight n ->
            classOf rows side n.item

        THole ->
            Exp


sideOf : Meta -> Side
sideOf m =
    case m of
        Pat ->
            PatSide

        AtPat ->
            PatSide

        _ ->
            ExpSide


qualified : String -> String -> String
qualified m x =
    case ( m, x ) of
        ( "Basics", "True" ) ->
            "basicsTrue"

        ( "Basics", "False" ) ->
            "basicsFalse"

        ( "Basics", "negate" ) ->
            "basicsNegate"

        _ ->
            "⟨some \"" ++ m ++ "\", \"" ++ x ++ "\"⟩"


matchOf : Ctx -> List ( Term, Term ) -> Result String String
matchOf ctx rules =
    case rules of
        [] ->
            Err "a case with no rules"

        ( p, b ) :: rest ->
            Result.map3
                (\pt bt restT -> ".mk (.mk " ++ paren pt ++ " " ++ paren bt ++ ") " ++ restT)
                (as_ ctx PatSide Pat p)
                (as_ ctx ExpSide Exp b)
                (if List.isEmpty rest then
                    Ok "none"

                 else
                    matchOf ctx rest |> Result.map (\m -> "(some (" ++ m ++ "))")
                )


combine : List (Result e a) -> Result e (List a)
combine =
    List.foldr (Result.map2 (::)) (Ok [])


{-| The sequence of a row, if its equivalent form has one, and the term with the sequence replaced
by a hole.
-}
splitNest : Term -> Maybe ( NestRight, Term )
splitNest t =
    case t of
        TNestRight n ->
            Just ( n, THole )

        TParen inner ->
            splitNest inner |> Maybe.map (\( n, rest ) -> ( n, TParen rest ))

        _ ->
            Nothing


definition : Dict String Row -> Row -> Result String String
definition rows r =
    case ( r.lean, r.equivalent ) of
        ( Generated g, Template t ) ->
            let
                paramNames =
                    List.map (\p -> ( refKey p.ref, p.name )) g.params

                itemNames =
                    g.seqParam
                        |> Maybe.map (\s -> List.indexedMap (\i rf -> ( refKey rf, "x" ++ String.fromInt i )) s.items)
                        |> Maybe.withDefault []

                ctx =
                    { rows = rows, names = Dict.fromList (paramNames ++ itemNames), hole = Nothing }

                seqType s =
                    case List.map (metaOf >> leanType) s.items of
                        [ one ] ->
                            "List " ++ one

                        many ->
                            "List (" ++ String.join " × " many ++ ")"

                seqPattern s =
                    case List.indexedMap (\i _ -> "x" ++ String.fromInt i) s.items of
                        [ one ] ->
                            one

                        many ->
                            "(" ++ String.join ", " many ++ ")"

                signature =
                    "def "
                        ++ g.name
                        ++ (g.seqParam |> Maybe.map (\s -> " (" ++ s.name ++ " : " ++ seqType s ++ ")") |> Maybe.withDefault "")
                        ++ String.concat (List.map (\p -> " (" ++ p.name ++ " : " ++ leanType (metaOf p.ref) ++ ")") g.params)
                        ++ " : "
                        ++ leanType g.result
                        ++ " :="

                doc =
                    "/-- Row \"" ++ plain (ToLatex.rowDerived rows r) ++ "\" (" ++ r.label ++ "): `" ++ plain (ToLatex.rowEquivalent rows r) ++ "`. -/"

                side =
                    sideOf g.result
            in
            case ( splitNest t, g.seqParam ) of
                ( Nothing, Nothing ) ->
                    as_ ctx side g.result t
                        |> Result.map (\body -> doc ++ "\n" ++ signature ++ "\n  " ++ body)

                ( Just ( n, outer ), Just s ) ->
                    let
                        itemSide =
                            side

                        itemClass =
                            Ok (classOf rows itemSide n.item)

                        goType cls =
                            seqType s ++ " → " ++ leanType cls
                    in
                    itemClass
                        |> Result.andThen
                            (\cls ->
                                let
                                    goCtx hole =
                                        { ctx | hole = Just hole }

                                    base =
                                        as_ ctx itemSide cls n.base

                                    lastCase =
                                        if n.wrapInner then
                                            base
                                                |> Result.andThen (\bt -> as_ (goCtx ( cls, bt )) itemSide cls n.item)
                                                |> Result.map (\it -> "\n    | [" ++ seqPattern s ++ "] => " ++ it)

                                        else
                                            Ok ""

                                    recHole =
                                        if n.wrapInner then
                                            ( Exp, ".atexp (.paren (go rest))" )

                                        else
                                            ( cls, "go rest" )

                                    consCase =
                                        as_ (goCtx recHole) itemSide cls n.item
                                            |> Result.map (\it -> "\n    | " ++ seqPattern s ++ " :: rest => " ++ it)

                                    outerBody =
                                        as_ (goCtx ( cls, "go " ++ s.name )) side g.result outer

                                    body =
                                        case g.whenEmpty of
                                            Just empty ->
                                                Result.map2
                                                    (\et ob -> "match " ++ s.name ++ " with\n  | [] => " ++ et ++ "\n  | _ => " ++ ob)
                                                    (as_ ctx side g.result empty)
                                                    outerBody

                                            Nothing ->
                                                outerBody
                                in
                                Result.map4
                                    (\b bt lc cc ->
                                        doc
                                            ++ "\n"
                                            ++ signature
                                            ++ "\n  "
                                            ++ b
                                            ++ "\nwhere\n  go : "
                                            ++ goType cls
                                            ++ "\n    | [] => "
                                            ++ bt
                                            ++ lc
                                            ++ cc
                                    )
                                    body
                                    base
                                    lastCase
                                    consCase
                            )

                _ ->
                    Err (r.label ++ ": a sequence row needs both a sequence term and a sequence parameter")

        _ ->
            Err (r.label ++ " is not a generated row")


{-| The generated rows in an order where each comes after the rows it uses.
-}
orderedRows : List Row -> List Row
orderedRows all =
    let
        generated =
            List.filter
                (\r ->
                    case r.lean of
                        Generated _ ->
                            True

                        HandWritten _ ->
                            False
                )
                all

        uses t =
            case t of
                TUse l args ->
                    l :: List.concatMap uses args

                TApp a b ->
                    uses a ++ uses b

                TParen a ->
                    uses a

                TLam a b ->
                    uses a ++ uses b

                TCase a rules ->
                    uses a ++ List.concatMap (\( p, b ) -> uses p ++ uses b) rules

                TPatCons a b ->
                    uses a ++ uses b

                TNestRight n ->
                    uses n.item ++ uses n.base

                _ ->
                    []

        usesOf r =
            case r.equivalent of
                Template t ->
                    uses t

                Computed _ ->
                    []

        go done todo =
            case List.partition (\r -> List.all (\l -> List.member l (List.map .label done)) (usesOf r)) todo of
                ( [], rest ) ->
                    done ++ rest

                ( ready, rest ) ->
                    go (done ++ ready) rest
    in
    go [] generated


{-| Every generated row as a Lean definition, in dependency order, separated by blank lines.
-}
definitions : List Row -> Result String String
definitions all =
    let
        rows =
            Dict.fromList (List.map (\r -> ( r.label, r )) all)
    in
    orderedRows all
        |> List.map (definition rows)
        |> combine
        |> Result.map (String.join "\n\n")


{-| The same definitions over the bare syntax (Src/Bare.lean, plan step 8): the bodies use only
constructor names, which the two syntaxes share, so only the types in the signatures change.
-}
bareDefinitions : List Row -> Result String String
bareDefinitions all =
    let
        bareTypes line =
            case Regex.fromString "\\b(Exp|AtExp|Pat|AtPat)\\b" of
                Just re ->
                    Regex.replace re (\m -> "B" ++ m.match) line

                Nothing ->
                    line

        isSignature line =
            String.startsWith "def " line || String.startsWith "  go : " line
    in
    definitions all
        |> Result.map
            (String.lines
                >> List.map
                    (\line ->
                        if isSignature line then
                            bareTypes line

                        else
                            line
                    )
                >> String.join "\n"
            )


{-| LaTeX of a row reduced to plain text, for doc comments.
-}
plain : String -> String
plain latex =
    let
        replace pattern f s =
            case Regex.fromString pattern of
                Just re ->
                    Regex.replace re f s

                Nothing ->
                    s
    in
    latex
        |> replace "\\\\phantom\\{(?:[^{}]|\\{[^{}]*\\})*\\}" (\_ -> "")
        |> replace "\\\\begin\\{array\\}\\[t\\]\\{@\\{\\}l@\\{\\}\\}|\\\\end\\{array\\}" (\_ -> "")
        |> String.replace "\\kw{\\textbackslash}" "\\"
        |> String.replace "\\kw{\\kwlb}" "{"
        |> String.replace "\\kw{\\kwrb}" "}"
        |> String.replace "\\\n" " "
        |> String.replace "\\&\\&" "&&"
        |> replace "\\\\kw\\{([^{}]*)\\}" (\m -> m.submatches |> List.head |> Maybe.andThen identity |> Maybe.withDefault "")
        |> String.replace "\\expm" "exp"
        |> String.replace "\\atexp" "atexp"
        |> String.replace "\\atpat" "atpat"
        |> String.replace "\\opv" "opv"
        |> String.replace "\\pat" "pat"
        |> String.replace "\\lab" "lab"
        |> String.replace "\\cdots" "..."
        |> String.replace "\\qquad" ""
        |> String.replace "\\quad" ""
        |> String.replace "\\geq" " >="
        |> String.replace "\\;" ""
        |> String.replace "\\\\" " "
        |> String.replace "\\ " " "
        |> String.replace "_" ""
        |> replace "\\s+" (\_ -> " ")
        |> String.trim
