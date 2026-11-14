module Translate.Fixity exposing
    ( Assoc(..)
    , Refusal
    , Tree(..)
    , check
    , group
    , groupChain
    , table
    , tree
    )

{-| Grouping operator chains by the book's fixities (plans/eco-parser.md, E5).

eco's parser keeps a chain `e0 op1 e1 ... opn en` flat (`Binops`). The translator groups it by
Figure `fig:core-fixities` of `definition/tex/syntax-core.tex` into nested binary applications, as
elm-syntax did, and refuses a chain the book does not allow (`res:core-operator-chain`): two
operators of equal precedence, with no operator of lower precedence between them, must both
associate to the left or both to the right. An operator outside the figure is refused as outside
the grammar.

-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Dict exposing (Dict)
import Translate.Region as Region exposing (Region)


type Assoc
    = Left
    | Right
    | Non


{-| Figure `fig:core-fixities`, exactly.
-}
table : Dict String { prec : Int, assoc : Assoc }
table =
    Dict.fromList
        [ ( "<<", { prec = 9, assoc = Left } )
        , ( ">>", { prec = 9, assoc = Right } )
        , ( "^", { prec = 8, assoc = Right } )
        , ( "*", { prec = 7, assoc = Left } )
        , ( "/", { prec = 7, assoc = Left } )
        , ( "//", { prec = 7, assoc = Left } )
        , ( "+", { prec = 6, assoc = Left } )
        , ( "-", { prec = 6, assoc = Left } )
        , ( "++", { prec = 5, assoc = Right } )
        , ( "::", { prec = 5, assoc = Right } )
        , ( "==", { prec = 4, assoc = Non } )
        , ( "/=", { prec = 4, assoc = Non } )
        , ( "<", { prec = 4, assoc = Non } )
        , ( ">", { prec = 4, assoc = Non } )
        , ( "<=", { prec = 4, assoc = Non } )
        , ( ">=", { prec = 4, assoc = Non } )
        , ( "&&", { prec = 3, assoc = Right } )
        , ( "||", { prec = 2, assoc = Right } )
        , ( "|>", { prec = 0, assoc = Left } )
        , ( "<|", { prec = 0, assoc = Right } )
        ]


type alias Refusal =
    { reason : String, at : Region }


{-| A grouped chain: an operand, or an operator applied to two grouped chains. `region` runs from
the start of the left operand to the end of the right one; `opRegion` is the operator's.
-}
type Tree
    = Operand Src.Expr
    | Apply { op : String, opRegion : Region, region : Region, left : Tree, right : Tree }


type alias Op =
    { name : String, region : Region }


{-| The chain of a `Binops`: its operands and operators in order.
-}
chainOf : ( Src.Expr, Src.C2 (A.Located String) ) -> List ( Src.Expr, Src.C2 (A.Located String) ) -> Src.Expr -> ( Src.Expr, List ( Op, Src.Expr ) )
chainOf first rest last =
    let
        pairs =
            first :: rest

        operands =
            List.map Tuple.first pairs ++ [ last ]

        ops =
            List.map (\( _, ( _, A.At r o ) ) -> { name = o, region = Region.fromA r }) pairs
    in
    ( Tuple.first first, List.map2 Tuple.pair ops (List.drop 1 operands) )


{-| The refusal of a chain, if any: an operator outside the table (`syntax:operator`), then a
breach of `res:core-operator-chain` (`syntax:core-operator-chain`), at the operator.
-}
check : ( Src.Expr, Src.C2 (A.Located String) ) -> List ( Src.Expr, Src.C2 (A.Located String) ) -> Src.Expr -> Maybe Refusal
check first rest last =
    checkChain (Tuple.second (chainOf first rest last) |> List.map Tuple.first)


checkChain : List Op -> Maybe Refusal
checkChain ops =
    case List.filter (\o -> not (Dict.member o.name table)) ops of
        o :: _ ->
            Just { reason = "syntax:operator", at = o.region }

        [] ->
            let
                fix o =
                    Dict.get o.name table |> Maybe.withDefault { prec = 0, assoc = Non }

                go l =
                    case l of
                        o :: more ->
                            let
                                f =
                                    fix o

                                -- the operators after o up to one of lower precedence, of o's
                                peers =
                                    takeWhile (\q -> (fix q).prec >= f.prec) more
                                        |> List.filter (\q -> (fix q).prec == f.prec)
                            in
                            case List.filter (\q -> not (f.assoc == (fix q).assoc && f.assoc /= Non)) peers of
                                q :: _ ->
                                    Just { reason = "syntax:core-operator-chain", at = q.region }

                                [] ->
                                    go more

                        [] ->
                            Nothing
            in
            go ops


takeWhile : (a -> Bool) -> List a -> List a
takeWhile p l =
    case l of
        x :: r ->
            if p x then
                x :: takeWhile p r

            else
                []

        [] ->
            []


{-| A `Binops` chain grouped, or its refusal.
-}
group : ( Src.Expr, Src.C2 (A.Located String) ) -> List ( Src.Expr, Src.C2 (A.Located String) ) -> Src.Expr -> Result Refusal Tree
group first rest last =
    let
        ( e0, pairs ) =
            chainOf first rest last
    in
    groupChain ( e0, pairs )


{-| `group` on a chain given as its first operand and its (operator, operand) pairs.
-}
groupChain : ( Src.Expr, List ( Op, Src.Expr ) ) -> Result Refusal Tree
groupChain ( e0, pairs ) =
    case checkChain (List.map Tuple.first pairs) of
        Just refusal ->
            Err refusal

        Nothing ->
            Ok (build (Operand e0) pairs)


{-| A `Binops` chain grouped. For a chain `check` refuses (which the front end has refused before
anything reads the tree) a non-associative operator groups to the left.
-}
tree : ( Src.Expr, Src.C2 (A.Located String) ) -> List ( Src.Expr, Src.C2 (A.Located String) ) -> Src.Expr -> Tree
tree first rest last =
    let
        ( e0, pairs ) =
            chainOf first rest last
    in
    build (Operand e0) pairs


{-| Precedence climbing: `lhs` followed by `pairs`, grouping every operator of at least `minPrec`.
-}
build : Tree -> List ( Op, Src.Expr ) -> Tree
build lhs pairs =
    Tuple.first (climb lhs pairs 0)


climb : Tree -> List ( Op, Src.Expr ) -> Int -> ( Tree, List ( Op, Src.Expr ) )
climb lhs pairs minPrec =
    case pairs of
        ( op, operand ) :: rest ->
            let
                f =
                    fixityOf op.name
            in
            if f.prec < minPrec then
                ( lhs, pairs )

            else
                let
                    ( rhs, after ) =
                        climbRight (Operand operand) rest f
                in
                climb (apply op lhs rhs) after minPrec

        [] ->
            ( lhs, [] )


{-| The right operand of an operator of fixity `f`: every following operator of higher
precedence, or of equal precedence that associates to the right, binds into it.
-}
climbRight : Tree -> List ( Op, Src.Expr ) -> { prec : Int, assoc : Assoc } -> ( Tree, List ( Op, Src.Expr ) )
climbRight rhs pairs f =
    case pairs of
        ( next, _ ) :: _ ->
            let
                g =
                    fixityOf next.name
            in
            if g.prec > f.prec then
                let
                    ( rhs2, after ) =
                        climb rhs pairs (f.prec + 1)
                in
                climbRight rhs2 after f

            else if g.prec == f.prec && g.assoc == Right then
                let
                    ( rhs2, after ) =
                        climb rhs pairs f.prec
                in
                climbRight rhs2 after f

            else
                ( rhs, pairs )

        [] ->
            ( rhs, [] )


fixityOf : String -> { prec : Int, assoc : Assoc }
fixityOf name =
    Dict.get name table |> Maybe.withDefault { prec = 9, assoc = Left }


apply : Op -> Tree -> Tree -> Tree
apply op left right =
    Apply
        { op = op.name
        , opRegion = op.region
        , region = { start = (regionOf left).start, end = (regionOf right).end }
        , left = left
        , right = right
        }


regionOf : Tree -> Region
regionOf t =
    case t of
        Operand (A.At r _) ->
            Region.fromA r

        Apply a ->
            a.region
