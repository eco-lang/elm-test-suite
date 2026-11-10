module Translate.Ir exposing
    ( Check
    , Decl(..)
    , Expr(..)
    , FloatLit
    , Name(..)
    , Pattern(..)
    , TestProgram
    , anyExpr
    , declBinders
    , patternBinders
    )

{-| The translator's representation of a test program after name resolution: every variable
occurrence knows the binding it refers to, every binding has a unique id, every integer literal has
an id by which inference records its type. Type annotations are kept, unconverted, for inference.
-}

import Dict exposing (Dict)
import Elm.Syntax.Node exposing (Node)
import Elm.Syntax.TypeAnnotation exposing (TypeAnnotation)


{-| A resolved name. `Local id name`: bound in the program (a pattern variable, a `let` or
top-level declaration) by the binding with that id. `Global module name`: bound in E0, written
qualified by the module in the source, or unqualified when the module is "". `UserCon`: a
constructor of a custom type of the program.
-}
type Name
    = Local Int String
    | Global String String
    | UserCon String


type alias FloatLit =
    { mantissa : String, exponent : Int }


type Expr
    = EUnit
    | EApp Expr (List Expr)
      -- occurrence id, operator
    | EBinop Int String Expr Expr
      -- occurrence id, name
    | EVar Int Name
    | ECon Name
    | EIf (List ( Expr, Expr )) Expr
    | EOp Int String
      -- literal id, the integer's decimal digits
    | EInt Int String
      -- an integer literal after number specialisation: at Float or not, its digits
    | EIntAt Bool String
    | EFloat FloatLit
    | ENeg Expr
    | EStr String
    | EChar Char
    | ETuple (List Expr)
    | EParen Expr
    | ELet (List Decl) Expr
    | ECase Expr (List ( Pattern, Expr ))
    | ELam (List Pattern) Expr
    | ERecord (List ( String, Expr ))
    | EList (List Expr)
    | EAccess Expr String
    | EAccessor String
      -- occurrence id, the record variable
    | EUpdate Int Name (List ( String, Expr ))


type Pattern
    = PWild
    | PUnit
    | PChar Char
    | PStr String
    | PInt String
    | PTuple (List Pattern)
    | PRecord (List ( String, Int ))
    | PCons Pattern Pattern
    | PList (List Pattern)
    | PVar String Int
    | PCon Name (List Pattern)
    | PAs Pattern String Int
    | PParen Pattern


{-| A declaration of a `let` or the top level: a function or value `name args = body` (its binder
id, and its annotation if any), or a pattern binding.
-}
type Decl
    = DFn { name : String, binder : Int, args : List Pattern, body : Expr, annotation : Maybe (Node TypeAnnotation) }
    | DPat Pattern Expr


type alias Check =
    { label : String
    , expected : String
    , expr : Expr
    }


{-| A test program: its custom types' constructors with their arities, its top-level declarations
other than `main`, and `main`'s `let`: the other declarations (`locals`) and the checks.
-}
type alias TestProgram =
    { cons : List ( String, Int )
    , types : Dict String { params : List String, constructors : List ( String, List (Node TypeAnnotation) ) }
    , aliases : Dict String { params : List String, annotation : Node TypeAnnotation }
    , defs : List Decl
    , locals : List Decl
    , checks : List Check
    }


patternBinders : Pattern -> List ( String, Int )
patternBinders p =
    case p of
        PTuple ps ->
            List.concatMap patternBinders ps

        PRecord fs ->
            fs

        PCons a b ->
            patternBinders a ++ patternBinders b

        PList ps ->
            List.concatMap patternBinders ps

        PVar x id ->
            [ ( x, id ) ]

        PCon _ ps ->
            List.concatMap patternBinders ps

        PAs q x id ->
            patternBinders q ++ [ ( x, id ) ]

        PParen q ->
            patternBinders q

        _ ->
            []


declBinders : Decl -> List ( String, Int )
declBinders d =
    case d of
        DFn f ->
            [ ( f.name, f.binder ) ]

        DPat p _ ->
            patternBinders p


{-| Whether an expression, or any expression within it (in declarations and case arms too),
satisfies the test.
-}
anyExpr : (Expr -> Bool) -> Expr -> Bool
anyExpr test e =
    test e
        || (case e of
                EApp f args ->
                    List.any (anyExpr test) (f :: args)

                EBinop _ _ a b ->
                    anyExpr test a || anyExpr test b

                EIf arms final ->
                    List.any (\( c, t ) -> anyExpr test c || anyExpr test t) arms || anyExpr test final

                ENeg x ->
                    anyExpr test x

                ETuple xs ->
                    List.any (anyExpr test) xs

                EParen x ->
                    anyExpr test x

                ELet decls body ->
                    List.any (anyDeclExpr test) decls || anyExpr test body

                ECase x arms ->
                    anyExpr test x || List.any (Tuple.second >> anyExpr test) arms

                ELam _ body ->
                    anyExpr test body

                ERecord fields ->
                    List.any (Tuple.second >> anyExpr test) fields

                EList xs ->
                    List.any (anyExpr test) xs

                EAccess x _ ->
                    anyExpr test x

                EUpdate _ _ fields ->
                    List.any (Tuple.second >> anyExpr test) fields

                _ ->
                    False
           )


{-| `anyExpr` over a declaration's expressions.
-}
anyDeclExpr : (Expr -> Bool) -> Decl -> Bool
anyDeclExpr test d =
    case d of
        DFn f ->
            anyExpr test f.body

        DPat _ x ->
            anyExpr test x
