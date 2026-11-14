module Translate.ToLean exposing (libraryDef, programDef, workerDef)

{-| Prints a specialised program as a Lean `TestProgram` in the helper notation of `Derived.lean`
(plans/elm-to-lean-translator.md, B.9). Every printer returns the text and the class of what it
printed; a coercion is inserted where the position needs another class.
-}

import Compiler.Core.Annotation as A
import Dict
import Translate.Ir exposing (..)
import Translate.Literal as Literal
import Translate.Parse as Parse
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
            case written name of
                ( Just m, k ) ->
                    ( AtExp, ".con " ++ qualifiedCon m k )

                ( Nothing, k ) ->
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


{-| A name as the source writes it: its qualifier, if any, and its last part. A constructor of
the module is written unqualified (its key's `M.` is the translator's).
-}
written : Name -> ( Maybe String, String )
written name =
    case name of
        Local _ x ->
            ( Nothing, x )

        Global "" x ->
            ( Nothing, x )

        Global m x ->
            ( Just m, x )

        Exposed _ x ->
            ( Nothing, x )

        UserCon k ->
            ( Nothing, String.split "." k |> List.reverse |> List.head |> Maybe.withDefault k )

        Foreign f ->
            ( f.qual, f.name )

        ForeignCon f ->
            ( f.qual, f.name )


plainName : Name -> String
plainName name =
    Tuple.second (written name)


varName : Name -> String
varName name =
    case ( name, written name ) of
        ( UserCon _, ( _, k ) ) ->
            "c " ++ str k

        ( ForeignCon _, ( Nothing, k ) ) ->
            "c " ++ str k

        ( ForeignCon _, ( Just m, k ) ) ->
            "(.atexp (.con " ++ qualifiedCon m k ++ "))"

        ( _, ( Nothing, x ) ) ->
            "v " ++ str x

        ( _, ( Just m, x ) ) ->
            "qv " ++ str m ++ " " ++ str x


{-| An operator of OT\_dyn: `^@Float` is `^` at Float, marked by number specialisation.
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
            case written name of
                ( Just m, k ) ->
                    ( AtPat, ".con " ++ qualifiedCon m k )

                ( Nothing, k ) ->
                    ( AtPat, "pcA " ++ str k )

        PCon name args ->
            case written name of
                ( Just m, k ) ->
                    ( Pat, ".con " ++ qualifiedCon m k ++ " " ++ listOf (List.map (pattern >> as_ AtPat) args) )

                ( Nothing, k ) ->
                    ( Pat, "pcon " ++ str k ++ " " ++ listOf (List.map (pattern >> as_ AtPat) args) )

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
naming its source; `library` is the core library values it names (plans/library-elm-texts.md).
-}
programDef : { defName : String, name : String, project : String } -> TestProgram -> List CheckKind -> Dict.Dict Int ( Bool, Payload ) -> Bool -> List String -> String
programDef info program kinds ports native library =
    let
        indent =
            "\n    "

        ( helpers, main ) =
            case List.reverse program.modules of
                m :: rest ->
                    ( List.reverse rest, Just m )

                [] ->
                    ( [], Nothing )

        paths =
            List.map .path program.modules
    in
    "/-- "
        ++ String.join ", " (List.reverse paths |> List.take 1 |> (\t -> t ++ List.filter (\p -> not (List.member p t)) paths))
        ++ " -/\ndef "
        ++ info.defName
        ++ " : Program := {\n  name := "
        ++ str info.name
        ++ ", source := "
        ++ str ("tests/" ++ info.project ++ "/src")
        ++ (if native then
                ", native := true"

            else
                ""
           )
        ++ (if List.isEmpty library then
                ""

            else
                ",\n  library := " ++ listOf (List.map str library)
           )
        ++ (case main of
                Just m ->
                    moduleFields ports "\n  " indent m

                Nothing ->
                    ""
           )
        ++ (if List.isEmpty helpers then
                ""

            else
                ",\n  helpers := ["
                    ++ String.join ","
                        (List.map
                            (\h ->
                                "\n   { name := "
                                    ++ str h.name
                                    ++ ", path := "
                                    ++ str h.path
                                    ++ moduleFields ports "\n     " (indent ++ "  ") h
                                    ++ " }"
                            )
                            helpers
                        )
                    ++ " ]"
           )
        ++ ",\n  checks := ["
        ++ String.join ","
            (List.map2
                (\c k -> indent ++ "chk " ++ lineKindName c.kind ++ " " ++ str c.text ++ " " ++ kindName k)
                program.checks
                kinds
            )
        ++ " ]"
        ++ (if program.meaning then
                ""

            else
                ",\n  meaning := false"
           )
        ++ " }"


{-| The Lean definition of a library module (plans/library-elm-texts.md, step 1),
`def <defName> : ModSrc := { ... }`, with a doc comment naming its file and its values.
-}
libraryDef : String -> ModuleIr -> String
libraryDef defName m =
    "/-- "
        ++ m.path
        ++ ": "
        ++ String.join ", " (List.concatMap (declBinders >> List.map Tuple.first) m.defs)
        ++ ". -/\ndef "
        ++ defName
        ++ " : ModSrc := {\n  name := "
        ++ str m.name
        ++ ", path := "
        ++ str m.path
        ++ moduleFields Dict.empty "\n  " "\n    " m
        ++ " }"


{-| A module's fields: its header's exposing list, its written imports, its custom types, aliases
and definitions.
-}
moduleFields : Dict.Dict Int ( Bool, Payload ) -> String -> String -> ModuleIr -> String
moduleFields ports sep indent m =
    ","
        ++ sep
        ++ "exposing := "
        ++ exposingLean m.exposes
        ++ ", imports := "
        ++ listOf (List.map importLean m.imports)
        ++ ","
        ++ sep
        ++ "types := "
        ++ listOf
            (List.map
                (\( t, d ) ->
                    "("
                        ++ str t
                        ++ ", "
                        ++ listOf (List.map (\( k, args ) -> "(" ++ str k ++ ", " ++ String.fromInt (List.length args) ++ ")") d.constructors)
                        ++ ")"
                )
                (Dict.toList m.types)
            )
        ++ ","
        ++ sep
        ++ "aliases := "
        ++ listOf
            (List.map
                (\( t, a ) ->
                    case Parse.recordType a.annotation of
                        Just fields ->
                            "(" ++ str t ++ ", some " ++ listOf (List.map (\( _, ( ( _, A.At _ l ), _ ) ) -> str l) fields) ++ ")"

                        Nothing ->
                            "(" ++ str t ++ ", none)"
                )
                (Dict.toList m.aliases)
            )
        ++ (if List.isEmpty m.ports then
                ""

            else
                ","
                    ++ sep
                    ++ "ports := "
                    ++ listOf
                        (List.map
                            (\pd ->
                                case Dict.get pd.binder ports of
                                    Just ( out, payload ) ->
                                        "("
                                            ++ str pd.name
                                            ++ ", "
                                            ++ (if out then
                                                    ".out"

                                                else
                                                    ".inn"
                                               )
                                            ++ ", "
                                            ++ payloadLean payload
                                            ++ ")"

                                    Nothing ->
                                        "(" ++ str pd.name ++ ", .out, .unit)"
                            )
                            m.ports
                        )
           )
        ++ ","
        ++ sep
        ++ "defs := ["
        ++ String.join "," (List.map (\d -> indent ++ decl d) m.defs)
        ++ " ]"


{-| A payload type as a `PTy` term (Eff/PTy.lean).
-}
payloadLean : Payload -> String
payloadLean p =
    case p of
        TyInt ->
            ".int"

        TyFloat ->
            ".float"

        TyBool ->
            ".bool"

        TyString ->
            ".string"

        TyBytes ->
            ".bytes"

        TyUnit ->
            ".unit"

        TyValue ->
            ".value"

        TyList a ->
            "(.list " ++ payloadLean a ++ ")"

        TyMaybe a ->
            "(.maybe " ++ payloadLean a ++ ")"

        TyArray a ->
            "(.array " ++ payloadLean a ++ ")"

        TyTuple2 a b ->
            "(.tuple2 " ++ payloadLean a ++ " " ++ payloadLean b ++ ")"

        TyTuple3 a b c ->
            "(.tuple3 " ++ payloadLean a ++ " " ++ payloadLean b ++ " " ++ payloadLean c ++ ")"

        TyRecord fields ->
            "(.record " ++ List.foldr (\( l, t ) rest -> "(.cons " ++ str l ++ " " ++ payloadLean t ++ " " ++ rest ++ ")") ".nil" fields ++ ")"


exposingLean : ExposingIr -> String
exposingLean x =
    case x of
        ExposeAll ->
            ".all"

        ExposeItems items ->
            "(.items "
                ++ listOf
                    (List.map
                        (\item ->
                            case item of
                                IVar v ->
                                    ".var " ++ str v

                                IOp o ->
                                    ".op " ++ str o

                                IType t ->
                                    ".tycon " ++ str t

                                IOpen t ->
                                    ".opened " ++ str t
                        )
                        items
                    )
                ++ ")"


{-| `import M [as Q] [exposing ...]`, read `import M as M` when there is no `as`.
-}
importLean : ImportIr -> String
importLean imp =
    "⟨"
        ++ str imp.modid
        ++ ", "
        ++ str (Maybe.withDefault imp.modid imp.alias)
        ++ ", "
        ++ (case imp.exposes of
                Just x ->
                    "some " ++ exposingLean x

                Nothing ->
                    "none"
           )
        ++ "⟩"


lineKindName : LineKind -> String
lineKindName k =
    case k of
        LCheck ->
            ".check"

        LNext ->
            ".next"

        LSame ->
            ".same"

        LNot ->
            ".not_"


{-| The worker test of a program whose `main` is a worker: its flags type and flags (absent flags
are null, A72) and its host; the checks are filled in by `#worker_theorems`.
-}
workerDef : { defName : String, name : String, project : String } -> Payload -> String -> Maybe ( String, String ) -> List String -> String
workerDef info flagsType flags host checkNots =
    "/-- The worker test of "
        ++ info.name
        ++ ". -/\ndef w"
        ++ String.dropLeft 1 info.defName
        ++ " : Prog.WorkerTest := {\n  prog := "
        ++ info.defName
        ++ ",\n  flagsType := "
        ++ payloadLean flagsType
        ++ ",\n  flags := "
        ++ flags
        ++ ",\n  host := "
        ++ (case host of
                Just ( o, i ) ->
                    ".echo " ++ str o ++ " " ++ str i

                Nothing ->
                    ".none"
           )
        ++ (if List.isEmpty checkNots then
                ""

            else
                ",\n  checkNots := [" ++ String.join ", " (List.map str checkNots) ++ "]"
           )
        ++ ",\n  checks := [] }"
