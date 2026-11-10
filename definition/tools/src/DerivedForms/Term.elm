module DerivedForms.Term exposing
    ( Block(..)
    , Condition(..)
    , Equivalent(..)
    , LeanParam
    , LeanSpec(..)
    , Meta(..)
    , NestLayout(..)
    , NestRight
    , Piece(..)
    , Ref(..)
    , Row
    , Term(..)
    , blockName
    )

{-| The template language of the derived forms of Appendix A of A Standard Definition of Elm?.

A row has two sides. The derived side is concrete syntax of the full language, only ever printed
as LaTeX, so it is a list of pieces. The equivalent side of a template row is bare abstract syntax
with metavariables, from which both the LaTeX of the book and the Lean of `Derived.lean` are
printed. The equivalent side of a computed row (the groupings) is given as pieces, and its Lean is
hand-written.

-}


{-| The phrase class of a metavariable.
-}
type Meta
    = Exp
    | AtExp
    | Pat
    | AtPat
    | Opv
    | Lab


{-| A metavariable as a row writes it: `\atexp`, `\expm_1`, `\expm_i` (the i-th item of the row's
sequence), `\expm'_i`.
-}
type Ref
    = Plain Meta
    | Indexed Meta Int
    | Item Meta
    | ItemPrimed Meta


{-| A piece of LaTeX. `Kw s` is `\kw{s}`, with `s` already escaped for LaTeX; `M r` is the macro of a
metavariable; `Raw s` is LaTeX as it stands (spacing, arrays, notes).
-}
type Piece
    = Kw String
    | M Ref
    | Raw String


type Term
    = TMeta Ref
    | TApp Term Term
    | TParen Term
    | TOp Ref
    | TOpLit String
    | TVarQual String String
    | TConQual String String
    | TVarOfLab Ref
    | TLam Term Term
    | TCase Term (List ( Term, Term ))
    | TNil
    | TRecordPat1 Ref
    | TPatCons Term Term
    | TUse String (List Term)
    | TNestRight NestRight
    | THole


{-| A row's sequence nested to the right: `item_1[ item_2[ ... item_n[ base ] ] ]`, each item with
the next in its hole. With `wrapInner`, each inner item (not the base) is put in parentheses in its
hole. The layout says how the book prints it: the items shown (1, 2 if `showSecond`, and n) and how
the elided ones are written.
-}
type alias NestRight =
    { item : Term
    , base : Term
    , wrapInner : Bool
    , showSecond : Bool
    , layout : NestLayout
    }


{-| `Inline`: the elision is written in the hole of the last item shown before it, as
`cdotsOpen ++ item_n ++ cdotsClose`. `Lines`: one item per line of an array, each indented by one
more `indent`, `afterSecond` after the second item, and the parentheses the inner items opened
closed together at the end by `closing`.
-}
type NestLayout
    = Inline { cdotsOpen : String, cdotsClose : String }
    | Lines { indent : String, afterSecond : String, closing : String }


type Block
    = Expressions
    | AtomicExpressions
    | AtomicPatterns
    | ValueBindings
    | Declarations
    | TopLevelDeclarations


blockName : Block -> String
blockName block =
    case block of
        Expressions ->
            "Expressions"

        AtomicExpressions ->
            "AtomicExpressions"

        AtomicPatterns ->
            "AtomicPatterns"

        ValueBindings ->
            "ValueBindings"

        Declarations ->
            "Declarations"

        TopLevelDeclarations ->
            "TopLevelDeclarations"


type Equivalent
    = Template Term
    | Computed (List Piece)


{-| The condition of a row, `(n\geq 2)`: after the equivalent form with the given spacing
(`\qquad`, `\quad`), or (for `Lines`) as the last line of its array.
-}
type Condition
    = NoCondition
    | After String String
    | LastLine String


type alias Row =
    { label : String
    , block : Block
    , derived : List Piece
    , equivalent : Equivalent
    , condition : Condition
    , lean : LeanSpec
    }


type alias LeanParam =
    { name : String, ref : Ref }


{-| How a row appears in `Derived.lean`. A generated row is one definition; its sequence, if it has
one, is the parameter `seqParam` (a `List` of the items' classes, a pair for two), and `whenEmpty` is
its value for an empty sequence when that is not the fold's base.
-}
type LeanSpec
    = Generated
        { name : String
        , params : List LeanParam
        , result : Meta
        , seqParam : Maybe { name : String, items : List Ref }
        , whenEmpty : Maybe Term
        }
    | HandWritten String
