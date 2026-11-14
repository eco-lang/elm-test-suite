module Translate.Ir exposing
    ( CheckLine
    , Decl(..)
    , ExportTable
    , ExposingIr(..)
    , Expr(..)
    , FloatLit
    , ImportIr
    , ItemIr(..)
    , LineKind(..)
    , ModuleIr
    , Name(..)
    , Pattern(..)
    , Payload(..)
    , TestProgram
    , anyDeclExpr
    , anyExpr
    , children
    , declBinders
    , globalOf
    , lineLabel
    , mainModule
    , patternBinders
    )

{-| The translator's representation of a test program after name resolution: every variable
occurrence knows the binding it refers to, every binding has a unique id, every integer literal has
an id by which inference records its type. Type annotations are kept, unconverted, for inference.
-}

import Compiler.IR.Source as Src
import Dict exposing (Dict)


{-| A resolved name. `Local id name`: bound in the module (a pattern variable, a `let` or
top-level declaration) by the binding with that id. `Global module name`: bound in E0, written
qualified by the module in the source, or unqualified when the module is "" (Basics).
`Exposed module name`: bound in E0 by `module`, written unqualified because an import's exposing
list brings it in (`text` after `import Html exposing (text)`); the reduced syntax keeps it as
written, and the module's imports resolve it (r:dm-import). `UserCon key`: a
constructor of a custom type or record alias of the module, by its key (its name, prefixed by
`M.` in a helper module `M`). `Foreign`: a value of another module of the program, by the id of
its binding there, as written (qualified or not). `ForeignCon`: a constructor of another module,
by its key, as written. Binding ids are unique across the program.
-}
type Name
    = Local Int String
    | Global String String
    | Exposed String String
    | UserCon String
    | Foreign { binder : Int, qual : Maybe String, name : String }
    | ForeignCon { key : String, qual : Maybe String, name : String }


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
    = DFn { name : String, binder : Int, args : List Pattern, body : Expr, annotation : Maybe Src.Type }
    | DPat Pattern Expr


{-| The directive of a CHECK line: CHECK and CHECK-DAG (read as CHECK, decision D9), CHECK-NEXT,
CHECK-SAME, CHECK-NOT (only in a test that stops with EXIT 1).
-}
type LineKind
    = LCheck
    | LNext
    | LSame
    | LNot


{-| A CHECK line of a test, as written.
-}
type alias CheckLine =
    { kind : LineKind
    , text : String
    }


{-| The module ("" for Basics written unqualified) and the name of a value or constructor of E0,
however the source writes it.
-}
globalOf : Name -> Maybe ( String, String )
globalOf name =
    case name of
        Global m x ->
            Just ( m, x )

        Exposed m x ->
            Just ( m, x )

        _ ->
            Nothing


{-| The label a CHECK line names: the text before its first `": "`, or the whole text; `Nothing`
for a line with a regular expression (`{{...}}`), which names no label, and for a CHECK-NOT.
-}
lineLabel : CheckLine -> Maybe String
lineLabel line =
    if String.contains "{{" line.text || line.kind == LNot then
        Nothing

    else
        case String.indexes ": " line.text of
            at :: _ ->
                Just (String.left at line.text)

            [] ->
                Just line.text


{-| An exposing list: `(..)`, or its items.
-}
type ExposingIr
    = ExposeAll
    | ExposeItems (List ItemIr)


{-| An exposing item: a value, an operator, a type by name, a type with its constructors.
-}
type ItemIr
    = IVar String
    | IOp String
    | IType String
    | IOpen String


{-| An import as written: `import M [as Q] [exposing ...]`.
-}
type alias ImportIr =
    { modid : String, alias : Maybe String, exposes : Maybe ExposingIr }


{-| What a module of the program exposes, for the modules that import it: its exposed values by
binding id, its exposed constructors (of types exposed with `(..)`, and of exposed record aliases)
by key, its exposed types by their canonical names, and its exposed aliases.
-}
type alias ExportTable =
    { values : Dict String Int
    , constructors : Dict String String
    , typeCons : Dict String (List String)
    , types : Dict String String
    , aliases : Dict String { params : List String, annotation : Src.Type }
    }


{-| A module of a test program: its name and file, its header's exposing list and its written
imports; its custom types' constructors with their arities, its custom types and aliases, and its
top-level declarations in the order written. `prefix` is "" for the main module and `M.` for a
helper `M`: the canonical names of its types and the keys of its constructors begin with it. The
types and aliases its imports bring in are `importedTypes` (a visible name, qualified or not, to a
canonical type name) and `importedAliases` (a visible name to the alias).
-}
type alias ModuleIr =
    { name : String
    , path : String
    , isPort : Bool
    , exposes : ExposingIr
    , imports : List ImportIr
    , prefix : String
    , cons : List ( String, Int )
    , types : Dict String { params : List String, constructors : List ( String, List Src.Type ) }
    , aliases : Dict String { params : List String, annotation : Src.Type }
    , importedTypes : Dict String String
    , importedAliases : Dict String { params : List String, annotation : Src.Type }
    , ports : List { name : String, binder : Int, annotation : Src.Type }
    , defs : List Decl
    }


{-| A port's payload type (static-modules.tex, sec:static-modules-ports), after alias expansion: a
record's fields sorted by label.
-}
type Payload
    = TyInt
    | TyFloat
    | TyBool
    | TyString
    | TyBytes
    | TyUnit
    | TyValue
    | TyList Payload
    | TyMaybe Payload
    | TyArray Payload
    | TyTuple2 Payload Payload
    | TyTuple3 Payload Payload Payload
    | TyRecord (List ( String, Payload ))


{-| A test program: its modules in program order (each after the modules it imports), the main
module last; its CHECK lines; and whether it is expected to have a meaning (`False` for a test
that stops with EXIT 1).
-}
type alias TestProgram =
    { modules : List ModuleIr
    , checks : List CheckLine
    , meaning : Bool
    }


{-| The main module of a program (the last).
-}
mainModule : TestProgram -> Maybe ModuleIr
mainModule p =
    List.head (List.reverse p.modules)


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


{-| The expressions immediately within an expression, the bodies of its declarations included.
-}
children : Expr -> List Expr
children e =
    let
        declExprs d =
            case d of
                DFn f ->
                    [ f.body ]

                DPat _ x ->
                    [ x ]
    in
    case e of
        EApp f args ->
            f :: args

        EBinop _ _ a b ->
            [ a, b ]

        EIf arms final ->
            List.concatMap (\( c, t ) -> [ c, t ]) arms ++ [ final ]

        ENeg x ->
            [ x ]

        ETuple xs ->
            xs

        EParen x ->
            [ x ]

        ELet decls body ->
            List.concatMap declExprs decls ++ [ body ]

        ECase x arms ->
            x :: List.map Tuple.second arms

        ELam _ body ->
            [ body ]

        ERecord fields ->
            List.map Tuple.second fields

        EList xs ->
            xs

        EAccess x _ ->
            [ x ]

        EUpdate _ _ fields ->
            List.map Tuple.second fields

        _ ->
            []
