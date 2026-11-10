module DerivedForms.ToLatex exposing (block, row, rowDerived, rowEquivalent)

{-| Prints the rows of Appendix A as the book's LaTeX: the `derivedforms` environment of `defn.sty`,
one `\dform{\citelabel{<label>}<derived>}{<equivalent>}` per row and `\hline` between rows.
-}

import Dict exposing (Dict)
import DerivedForms.Term exposing (..)


macro : Meta -> String
macro meta =
    case meta of
        Exp ->
            "\\expm"

        AtExp ->
            "\\atexp"

        Pat ->
            "\\pat"

        AtPat ->
            "\\atpat"

        Opv ->
            "\\opv"

        Lab ->
            "\\lab"


{-| A metavariable; `idx` is the index an `Item` takes where it is printed ("1", "2" or "n").
-}
ref : String -> Ref -> String
ref idx r =
    case r of
        Plain m ->
            macro m

        Indexed m k ->
            macro m ++ "_" ++ String.fromInt k

        Item m ->
            macro m ++ "_" ++ idx

        ItemPrimed m ->
            macro m ++ "'_" ++ idx


refKey : Ref -> String
refKey r =
    case r of
        Plain m ->
            "p" ++ macro m

        Indexed m k ->
            "x" ++ macro m ++ String.fromInt k

        Item m ->
            "i" ++ macro m

        ItemPrimed m ->
            "j" ++ macro m


kw : String -> String
kw s =
    "\\kw{" ++ s ++ "}"


pieces : (Ref -> String) -> List Piece -> String
pieces showRef ps =
    ps
        |> List.map
            (\p ->
                case p of
                    Kw s ->
                        kw s

                    M r ->
                        showRef r

                    Raw s ->
                        s
            )
        |> String.concat


type alias Ctx =
    { rows : Dict String Row
    , idx : String
    , hole : String
    }


term : Ctx -> Term -> String
term ctx t =
    case t of
        TMeta r ->
            ref ctx.idx r

        TApp f a ->
            term ctx f ++ "\\ " ++ term ctx a

        TParen e ->
            kw "(" ++ term ctx e ++ kw ")"

        TOp r ->
            kw "(" ++ ref ctx.idx r ++ kw ")"

        TOpLit s ->
            kw "(" ++ kw s ++ kw ")"

        TVarQual m x ->
            kw (m ++ "." ++ x)

        TConQual m x ->
            kw (m ++ "." ++ x)

        TVarOfLab r ->
            ref ctx.idx r

        TLam p e ->
            kw "\\textbackslash" ++ term ctx p ++ "\\ " ++ kw "->" ++ "\\ " ++ term ctx e

        TCase e rules ->
            let
                scrutinee =
                    term ctx e

                rule i ( p, b ) =
                    (if i == 0 then
                        kw "case" ++ "\\ " ++ scrutinee ++ "\\ " ++ kw "of" ++ "\\ "

                     else
                        "\\phantom{" ++ kw "case" ++ "\\ " ++ scrutinee ++ "\\ " ++ kw "of" ++ "}\\ " ++ kw ";" ++ "\\ "
                    )
                        ++ term ctx p
                        ++ "\\ "
                        ++ kw "->"
                        ++ "\\ "
                        ++ term ctx b
            in
            "\\begin{array}[t]{@{}l@{}}\n         "
                ++ String.join "\\\\\n         " (List.indexedMap rule rules)
                ++ "\n       \\end{array}"

        TNil ->
            kw "[ ]"

        TRecordPat1 r ->
            kw "\\kwlb" ++ "\\ " ++ ref ctx.idx r ++ "\\ " ++ kw "\\kwrb"

        TPatCons p q ->
            term ctx p ++ "\\ " ++ kw "::" ++ "\\ " ++ term ctx q

        TUse label args ->
            use ctx label args

        TNestRight n ->
            nestInline ctx n

        THole ->
            ctx.hole


{-| Another row applied to arguments: its derived form with the arguments in place of its
metavariables, as the book writes it (`df:and` reads `if exp1 then exp2 else Basics.False`).
-}
use : Ctx -> String -> List Term -> String
use ctx label args =
    case Dict.get label ctx.rows of
        Just r ->
            case r.lean of
                Generated g ->
                    let
                        shown arg param =
                            case ( param.ref, arg ) of
                                ( Plain Opv, TOpLit s ) ->
                                    kw s

                                _ ->
                                    term ctx arg

                        subst =
                            List.map2 (\param arg -> ( refKey param.ref, shown arg param )) g.params args
                                |> Dict.fromList
                    in
                    pieces (\rf -> Dict.get (refKey rf) subst |> Maybe.withDefault (ref ctx.idx rf)) r.derived

                HandWritten _ ->
                    "?" ++ label

        Nothing ->
            "?" ++ label


nestInline : Ctx -> NestRight -> String
nestInline ctx n =
    case n.layout of
        Inline { cdotsOpen, cdotsClose } ->
            let
                last =
                    term { ctx | idx = "n", hole = term ctx n.base } n.item

                elided =
                    cdotsOpen ++ last ++ cdotsClose

                shown =
                    if n.showSecond then
                        [ "1", "2" ]

                    else
                        [ "1" ]
            in
            List.foldr (\idx inner -> term { ctx | idx = idx, hole = inner } n.item) elided shown

        Lines _ ->
            nestLines ctx n Nothing


nestLines : Ctx -> NestRight -> Maybe String -> String
nestLines ctx n condition =
    case n.layout of
        Lines { indent, afterSecond, closing } ->
            let
                open =
                    if n.wrapInner then
                        kw "("

                    else
                        ""

                first =
                    term { ctx | idx = "1", hole = open } n.item

                second =
                    if n.showSecond then
                        [ indent ++ term { ctx | idx = "2", hole = open } n.item ++ afterSecond ]

                    else
                        []

                depth =
                    1 + List.length second

                last =
                    String.repeat depth indent
                        ++ term { ctx | idx = "n", hole = term ctx n.base } n.item
                        ++ "\n           "
                        ++ closing

                lines =
                    (first :: second) ++ [ last ] ++ (condition |> Maybe.map List.singleton |> Maybe.withDefault [])
            in
            "\\begin{array}[t]{@{}l@{}}\n         "
                ++ String.join "\\\\\n         " lines
                ++ "\n       \\end{array}"

        Inline _ ->
            nestInline ctx n


{-| The derived side of a row, as LaTeX.
-}
rowDerived : Dict String Row -> Row -> String
rowDerived _ r =
    pieces (ref "i") r.derived


{-| The equivalent side of a row, as LaTeX, with its condition.
-}
rowEquivalent : Dict String Row -> Row -> String
rowEquivalent rows r =
    let
        ctx =
            { rows = rows, idx = "i", hole = "" }
    in
    case ( r.equivalent, r.condition ) of
        ( Template (TNestRight n), LastLine c ) ->
            nestLines ctx n (Just c)

        ( Template t, After space c ) ->
            term ctx t ++ "\n       " ++ space ++ " " ++ c

        ( Template t, _ ) ->
            term ctx t

        ( Computed ps, _ ) ->
            pieces (ref "i") ps


{-| One row: `\dform{\citelabel{<label>}<derived>}` and, on the next line, `{<equivalent>}`.
-}
row : Dict String Row -> Row -> String
row rows r =
    "\\dform{\\citelabel{" ++ r.label ++ "}" ++ rowDerived rows r ++ "}\n      {" ++ rowEquivalent rows r ++ "}"


{-| The rows of one block, as a `derivedforms` environment.
-}
block : Dict String Row -> List Row -> String
block rows rs =
    "\\begin{derivedforms}\n" ++ String.join "\n\\hline\n" (List.map (row rows) rs) ++ "\n\\end{derivedforms}"
