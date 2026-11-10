module Translate.ToLean exposing (programDef)

{-| Prints a specialised program as a Lean `TestProgram` in the helper notation of `Derived.lean`
(plans/elm-to-lean-translator.md, B.9). Every printer returns the text and the class of what it
printed; a coercion is inserted where the position needs another class.
-}

import Translate.Ir exposing (..)
import Translate.Literal as Literal
import Translate.Specialise exposing (CheckKind(..))


type Cls
    = Exp
    | AtExp
    | Pat
    | AtPat


paren : String -> String
paren s =
    if String.contains " " s && not (String.startsWith "(" s && String.endsWith ")" s && balanced (String.slice 1 -1 s)) then
        "(" ++ s ++ ")"

    else
        s


{-| Whether parentheses are balanced throughout, so that "(a) (b)" is not taken as one group.
-}
balanced : String -> Bool
balanced s =
    String.foldl
        (\c ( depth, ok ) ->
            if not ok then
                ( depth, False )

            else if c == '(' then
                ( depth + 1, True )

            else if c == ')' then
                ( depth - 1, depth - 1 >= 0 )

            else
                ( depth, True )
        )
        ( 0, True )
        s
        |> (\( d, ok ) -> ok && d == 0)


as_ : Cls -> ( Cls, String ) -> String
as_ want ( have, text ) =
    if want == have then
        text

    else
        case ( have, want ) of
            ( AtExp, Exp ) ->
                ".atexp " ++ paren text

            ( Exp, AtExp ) ->
                "A " ++ paren text

            ( AtPat, Pat ) ->
                "P " ++ paren text

            ( Pat, AtPat ) ->
                "PA " ++ paren text

            _ ->
                text


str : String -> String
str =
    Literal.leanString


listOf : List String -> String
listOf xs =
    "[" ++ String.join ", " xs ++ "]"


qualifiedCon : String -> String -> String
qualifiedCon m k =
    "⟨some " ++ str m ++ ", " ++ str k ++ "⟩"


expr : Expr -> ( Cls, String )
expr e =
    case e of
        EUnit ->
            ( AtExp, ".unit" )

        EApp f args ->
            ( Exp, "ap " ++ paren (as_ Exp (expr f)) ++ " " ++ listOf (List.map (expr >> as_ Exp) args) )

        EBinop _ "&&" a b ->
            ( Exp, "andalso " ++ paren (as_ Exp (expr a)) ++ " " ++ paren (as_ Exp (expr b)) )

        EBinop _ "||" a b ->
            ( Exp, "orelse " ++ paren (as_ Exp (expr a)) ++ " " ++ paren (as_ Exp (expr b)) )

        EBinop _ op a b ->
            ( Exp, "bin " ++ str (leanOp op) ++ " " ++ paren (as_ Exp (expr a)) ++ " " ++ paren (as_ Exp (expr b)) )

        EVar _ name ->
            ( Exp, varName name )

        ECon name ->
            case name of
                UserCon k ->
                    ( Exp, "c " ++ str k )

                Global "" k ->
                    ( Exp, "c " ++ str k )

                Global m k ->
                    ( AtExp, ".con " ++ qualifiedCon m k )

                Local _ k ->
                    ( Exp, "c " ++ str k )

        EIf [ ( c, t ) ] final ->
            ( Exp, "ifte " ++ paren (as_ Exp (expr c)) ++ " " ++ paren (as_ Exp (expr t)) ++ " " ++ paren (as_ Exp (expr final)) )

        EIf arms final ->
            ( Exp
            , "ifChain "
                ++ listOf (List.map (\( c, t ) -> "(" ++ as_ Exp (expr c) ++ ", " ++ as_ Exp (expr t) ++ ")") arms)
                ++ " "
                ++ paren (as_ Exp (expr final))
            )

        EOp _ op ->
            ( AtExp, ".op " ++ str (leanOp op) )

        EInt _ digits ->
            ( Exp, "i " ++ digits )

        EIntAt False digits ->
            ( Exp, "i " ++ digits )

        EIntAt True digits ->
            ( AtExp, ".scon (.intF " ++ digits ++ ")" )

        EFloat f ->
            ( AtExp, ".scon (.float " ++ f.mantissa ++ " (" ++ String.fromInt f.exponent ++ "))" )

        ENeg x ->
            ( AtExp, "neg " ++ paren (as_ AtExp (expr x)) )

        EStr s ->
            ( Exp, "str " ++ str s )

        EChar c ->
            ( AtExp, "chA " ++ Literal.leanChar c )

        ETuple [ a, b ] ->
            ( Exp, "tup2 " ++ paren (as_ Exp (expr a)) ++ " " ++ paren (as_ Exp (expr b)) )

        ETuple [ a, b, c ] ->
            ( Exp, "tup3 " ++ paren (as_ Exp (expr a)) ++ " " ++ paren (as_ Exp (expr b)) ++ " " ++ paren (as_ Exp (expr c)) )

        ETuple _ ->
            ( AtExp, ".unit" )

        EParen x ->
            ( AtExp, ".paren " ++ paren (as_ Exp (expr x)) )

        ELet decls body ->
            ( Exp, "letDefs " ++ listOf (List.map decl decls) ++ " " ++ paren (as_ Exp (expr body)) )

        ECase s rules ->
            ( Exp
            , "caseOf "
                ++ paren (as_ Exp (expr s))
                ++ " "
                ++ listOf (List.map (\( p, b ) -> "(" ++ as_ Pat (pattern p) ++ ", " ++ as_ Exp (expr b) ++ ")") rules)
            )

        ELam ps body ->
            ( Exp, "lams " ++ listOf (List.map (pattern >> as_ AtPat) ps) ++ " " ++ paren (as_ Exp (expr body)) )

        ERecord fields ->
            ( Exp, "recE " ++ listOf (List.map (\( f, x ) -> "(" ++ str f ++ ", " ++ as_ Exp (expr x) ++ ")") fields) )

        EList xs ->
            ( Exp, "listE " ++ listOf (List.map (expr >> as_ Exp) xs) )

        EAccess x f ->
            ( AtExp, "access " ++ paren (as_ AtExp (expr x)) ++ " " ++ str f )

        EAccessor f ->
            ( AtExp, "accessor " ++ str f )

        EUpdate _ name fields ->
            ( Exp
            , "updE "
                ++ str (plainName name)
                ++ " "
                ++ listOf (List.map (\( f, x ) -> "(" ++ str f ++ ", " ++ as_ Exp (expr x) ++ ")") fields)
            )


plainName : Name -> String
plainName name =
    case name of
        Local _ x ->
            x

        Global _ x ->
            x

        UserCon k ->
            k


varName : Name -> String
varName name =
    case name of
        Local _ x ->
            "v " ++ str x

        Global "" x ->
            "v " ++ str x

        Global m x ->
            "qv " ++ str m ++ " " ++ str x

        UserCon k ->
            "c " ++ str k


{-| An operator of OT_dyn: `^@Float` is `^` at Float, marked by number specialisation.
-}
leanOp : String -> String
leanOp op =
    if op == "^@Float" then
        "^"

    else
        op


pattern : Pattern -> ( Cls, String )
pattern p =
    case p of
        PWild ->
            ( AtPat, "pw" )

        PUnit ->
            ( AtPat, ".unit" )

        PChar c ->
            ( AtPat, "pchar " ++ Literal.leanChar c )

        PStr s ->
            ( AtPat, ".scon (.str " ++ str s ++ ")" )

        PInt digits ->
            ( AtPat, "pint " ++ digits )

        PTuple [ a, b ] ->
            ( AtPat, "ptup2 " ++ paren (as_ Pat (pattern a)) ++ " " ++ paren (as_ Pat (pattern b)) )

        PTuple [ a, b, c ] ->
            ( AtPat, "ptup3 " ++ paren (as_ Pat (pattern a)) ++ " " ++ paren (as_ Pat (pattern b)) ++ " " ++ paren (as_ Pat (pattern c)) )

        PTuple _ ->
            ( AtPat, ".unit" )

        PRecord fields ->
            ( AtPat, "precord " ++ listOf (List.map (Tuple.first >> str) fields) )

        PCons a b ->
            ( Pat, ".cons " ++ paren (as_ Pat (pattern a)) ++ " " ++ paren (as_ Pat (pattern b)) )

        PList ps ->
            ( AtPat, "listP " ++ listOf (List.map (pattern >> as_ Pat) ps) )

        PVar x _ ->
            ( AtPat, "pv " ++ str x )

        PCon name [] ->
            case name of
                Global m k ->
                    if m == "" then
                        ( AtPat, "pcA " ++ str k )

                    else
                        ( AtPat, ".con " ++ qualifiedCon m k )

                _ ->
                    ( AtPat, "pcA " ++ str (plainName name) )

        PCon name args ->
            case name of
                Global m k ->
                    if m == "" then
                        ( Pat, "pcon " ++ str k ++ " " ++ listOf (List.map (pattern >> as_ AtPat) args) )

                    else
                        ( Pat, ".con " ++ qualifiedCon m k ++ " " ++ listOf (List.map (pattern >> as_ AtPat) args) )

                _ ->
                    ( Pat, "pcon " ++ str (plainName name) ++ " " ++ listOf (List.map (pattern >> as_ AtPat) args) )

        PAs q x _ ->
            ( Pat, ".as " ++ paren (as_ Pat (pattern q)) ++ " " ++ str x )

        PParen q ->
            ( AtPat, ".paren " ++ paren (as_ Pat (pattern q)) )


decl : Decl -> String
decl d =
    case d of
        DFn f ->
            ".fn " ++ str f.name ++ " " ++ listOf (List.map (pattern >> as_ AtPat) f.args) ++ " " ++ paren (as_ Exp (expr f.body))

        DPat p x ->
            ".pat " ++ paren (as_ AtPat (pattern p)) ++ " " ++ paren (as_ Exp (expr x))


kindName : CheckKind -> String
kindName k =
    case k of
        KInt ->
            ".int"

        KFloat ->
            ".float"

        KString ->
            ".string"

        KChar ->
            ".char"

        KData ->
            ".data"

        KFunction ->
            ".function"


{-| The Lean definition of a test program, `def <defName> : TestProgram := { ... }`, with a doc comment
naming its source.
-}
programDef : { defName : String, name : String, project : String } -> TestProgram -> List CheckKind -> Bool -> String
programDef info program kinds native =
    let
        indent =
            "\n    "
    in
    "/-- tests/"
        ++ info.project
        ++ "/src/"
        ++ info.name
        ++ ".elm -/\ndef "
        ++ info.defName
        ++ " : Program := {\n  name := "
        ++ str info.name
        ++ ", source := "
        ++ str ("tests/" ++ info.project ++ "/src")
        ++ (if native then ", native := true" else "")
        ++ ",\n  cons := "
        ++ listOf (List.map (\( k, n ) -> "(" ++ str k ++ ", " ++ String.fromInt n ++ ")") program.cons)
        ++ ",\n  defs := ["
        ++ String.join "," (List.map (\d -> indent ++ decl d) program.defs)
        ++ " ],\n  locals := ["
        ++ String.join "," (List.map (\d -> indent ++ decl d) program.locals)
        ++ " ],\n  checks := ["
        ++ String.join ","
            (List.map2
                (\c k -> indent ++ "ckk " ++ str c.label ++ " " ++ str c.expected ++ " " ++ kindName k ++ " " ++ paren (as_ Exp (expr c.expr)))
                program.checks
                kinds
            )
        ++ " ] }"
