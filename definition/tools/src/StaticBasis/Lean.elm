module StaticBasis.Lean exposing (outPath, toLean)

{-| The static basis of Appendix C as Lean (plans/lean-full-definition/step-09-static-semantics.md,
section 6): `StandardElmMech/Generated/StaticBasis.lean`, written by the extractor from the same
`Basis` it writes to `static-basis.json`. Schemes are written in canonical form (bound variables
`bnd 0, bnd 1, ...` in order of first occurrence, rows sorted by label), and the file checks that
they are, by the kernel.
-}

import Dict exposing (Dict)
import StaticBasis.Json exposing (Basis, DefaultImport, ExposedItem(..), Exposing(..), Interface)
import StaticBasis.Latex exposing (Scheme, TEntry, Ty(..), VEntry)


outPath : String
outPath =
    "definition/mechanisation/standard-elm-mech/StandardElmMech/Generated/StaticBasis.lean"


builtins : List String
builtins =
    [ "Int", "Float", "Char", "String", "Unit", "List", "Tuple2", "Tuple3" ]


leanName : String -> String
leanName key =
    "t" ++ key


str : String -> String
str s =
    "\"" ++ s ++ "\""


classOf : String -> String
classOf a =
    if String.startsWith "number" a then
        ".num"

    else if String.startsWith "comparable" a then
        ".comp"

    else if String.startsWith "appendable" a then
        ".app"

    else if String.startsWith "compappend" a then
        ".capp"

    else
        ".any"


sortedFields : List ( String, Ty ) -> List ( String, Ty )
sortedFields =
    List.sortBy Tuple.first


varsOf : Ty -> List String
varsOf t =
    case t of
        TyVar a ->
            [ a ]

        TyCon _ args ->
            List.concatMap varsOf args

        TyFn a b ->
            varsOf a ++ varsOf b

        TyRecord fs ->
            List.concatMap (Tuple.second >> varsOf) (sortedFields fs)


dedup : List String -> List String
dedup xs =
    List.foldl
        (\x acc ->
            if List.member x acc then
                acc

            else
                acc ++ [ x ]
        )
        []
        xs


tyL : Dict String Int -> Ty -> String
tyL idx t =
    case t of
        TyVar a ->
            case Dict.get a idx of
                Just i ->
                    "(.var (.bnd " ++ String.fromInt i ++ " " ++ classOf a ++ "))"

                Nothing ->
                    "(.var (.named " ++ str a ++ "))"

        TyCon c args ->
            "(.con [" ++ String.join ", " (List.map (tyL idx) args) ++ "] " ++ leanName c ++ ")"

        TyFn a b ->
            "(.fn " ++ tyL idx a ++ " " ++ tyL idx b ++ ")"

        TyRecord fs ->
            "(.record [" ++ String.join ", " (List.map (\( l, ft ) -> "(" ++ str l ++ ", " ++ tyL idx ft ++ ")") (sortedFields fs)) ++ "] none)"


schemeL : Scheme -> String
schemeL s =
    let
        vars =
            dedup (varsOf s.body) |> List.filter (\a -> List.member a s.forall)

        idx =
            Dict.fromList (List.indexedMap (\i a -> ( a, i )) vars)

        bound =
            List.indexedMap (\i a -> ".ty (.bnd " ++ String.fromInt i ++ " " ++ classOf a ++ ")") vars
    in
    "⟨[" ++ String.join ", " bound ++ "], " ++ tyL idx s.body ++ "⟩"


statusL : String -> String
statusL s =
    if s == "c" then
        ".c"

    else
        ".v"


veL : String -> List VEntry -> String
veL indent ve =
    if List.isEmpty ve then
        "[]"

    else
        "[ "
            ++ String.join (",\n" ++ indent ++ "  ") (List.map (\e -> "(" ++ str e.name ++ ", (" ++ schemeL e.scheme ++ ", " ++ statusL e.status ++ "))") ve)
            ++ " ]"


teL : String -> List TEntry -> String
teL indent te =
    if List.isEmpty te then
        "[]"

    else
        "[ "
            ++ String.join (",\n" ++ indent ++ "  ")
                (List.map (\e -> "(" ++ str e.tycon ++ ", (" ++ leanName e.typeName ++ ".toFcn,\n" ++ indent ++ "    " ++ veL (indent ++ "    ") e.ve ++ "))") te)
            ++ " ]"


ifaceName : String -> String
ifaceName m =
    "I_" ++ String.replace "." "_" m


itemL : ExposedItem -> String
itemL it =
    case it of
        ExpValue x ->
            ".var " ++ str x

        ExpOp o ->
            ".op " ++ str o

        ExpType c ->
            ".ty " ++ str c

        ExpTypeAll c ->
            ".tyAll " ++ str c


exposingL : Maybe Exposing -> String
exposingL ex =
    case ex of
        Nothing ->
            "none"

        Just ExposingAll ->
            "some .all"

        Just (ExposingItems items) ->
            "some (.items [" ++ String.join ", " (List.map itemL items) ++ "])"


importL : DefaultImport -> String
importL i =
    "⟨"
        ++ str i.module_
        ++ ", "
        ++ (case i.as_ of
                Nothing ->
                    "none"

                Just a ->
                    "some " ++ str a
           )
        ++ ", "
        ++ exposingL i.exposing_
        ++ "⟩"


toLean : Basis -> String
toLean b =
    let
        tyNameDefs =
            List.indexedMap
                (\i r ->
                    if List.member r.key builtins then
                        "example : " ++ leanName r.key ++ " = ⟨" ++ String.fromInt i ++ ", " ++ String.fromInt r.arity ++ "⟩ := rfl"

                    else
                        "def " ++ leanName r.key ++ " : TyName := ⟨" ++ String.fromInt i ++ ", " ++ String.fromInt r.arity ++ "⟩"
                )
                b.typeNames

        ifaceDef m =
            "/-- ME0(" ++ m.module_ ++ ") (" ++ m.library ++ "). -/\ndef " ++ ifaceName m.module_ ++ " : IEnv where\n  TE := " ++ teL "    " m.te ++ "\n  VE := " ++ veL "    " m.ve

        opRow o =
            "(" ++ str o.op ++ ", (" ++ schemeL o.scheme ++ ", " ++ statusL o.status ++ "))"

        hiddenRow h =
            case ( h.kind, h.typeName ) of
                ( "constructor", Just tn ) ->
                    Just ("(" ++ str h.module_ ++ ", " ++ str h.name ++ ", " ++ leanName tn ++ ")")

                _ ->
                    Nothing
    in
    String.join "\n"
        ([ "/-"
         , "  A Standard Definition of Elm? Mechanisation: the static basis of Appendix C (appendix-static-basis.tex)"
         , "  and the default imports (fig:default-imports), plan step 9 (section 6)."
         , ""
         , "  GENERATED by definition/tools/src/ExtractStaticBasis.elm from the same extraction as"
         , "  definition/mechanisation/static-basis.json; do not edit. Schemes are written in canonical form;"
         , "  the theorems at the end check that they are, and that every type name of ME0 is in T0."
         , "-/"
         , "import StandardElmMech.Stat.Schemes"
         , "import StandardElmMech.Src.Restrictions"
         , ""
         , "namespace StandardElm.Stat"
         , ""
         , "/-! ## T0 (fig:static-basis-tynames) -/"
         , ""
         ]
            ++ tyNameDefs
            ++ [ ""
               , "def T0 : List TyName := [" ++ String.join ", " (List.map (.key >> leanName) b.typeNames) ++ "]"
               , ""
               , "/-! ## E0: List and its constructors -/"
               , ""
               , "def E0 : IEnv where"
               , "  TE := " ++ teL "    " b.e0.te
               , "  VE := " ++ veL "    " b.e0.ve
               , ""
               , "/-! ## ME0 (sec:appendix-static-basis-modenv) -/"
               , ""
               ]
            ++ List.map ifaceDef b.modules
            ++ [ ""
               , "def ME0 : ModEnv :="
               , "  [ " ++ String.join ",\n    " (List.map (\m -> "(" ++ str m.module_ ++ ", " ++ ifaceName m.module_ ++ ")") b.modules) ++ " ]"
               , ""
               , "/-! ## The static operator table and the operators of each module -/"
               , ""
               , "def OTstatList : FMap Op (Scheme × IdStatus) :="
               , "  [ " ++ String.join ",\n    " (List.map opRow b.operators) ++ " ]"
               , ""
               , "/-- OT_stat (sec:static-core-projection). -/"
               , "def OTstat (o : Op) : Option (Scheme × IdStatus) := FMap.find? OTstatList o"
               , ""
               , "def smopsList : FMap ModId (List Op) :="
               , "  [ " ++ String.join ",\n    " (List.map (\m -> "(" ++ str m.module_ ++ ", [" ++ String.join ", " (List.map str m.ops) ++ "])") b.modules) ++ " ]"
               , ""
               , "/-- The operators a module of the basis provides (sec:static-modules-rules, r:sm-item-op). -/"
               , "def smops (m : ModId) : List Op := (FMap.find? smopsList m).getD []"
               , ""
               , "/-- The hidden constructors of Appendix C: module, constructor, type name. -/"
               , "def hiddenCons : List (ModId × String × TyName) := [" ++ String.join ", " (List.filterMap hiddenRow b.hidden) ++ "]"
               , ""
               , "/-! ## The default imports (fig:default-imports) -/"
               , ""
               , "def defaultImports : List Src.BImport :="
               , "  [ " ++ String.join ",\n    " (List.map importL b.defaultImports) ++ " ]"
               , ""
               , "/-! ## Checks -/"
               , ""
               , "def IEnv.canonB (I : IEnv) : Bool :="
               , "  I.VE.all (fun p => p.2.1.canon == p.2.1) && I.TE.all (fun p => p.2.2.all fun q => q.2.1.canon == q.2.1)"
               , ""
               , "/-- Every scheme of ME0, E0 and OT_stat is canonical. -/"
               , "theorem ME0_canon : (ME0.all fun p => p.2.canonB) && E0.canonB && OTstatList.all (fun p => p.2.1.canon == p.2.1) = true := by"
               , "  decide +kernel"
               , ""
               , "/-- tynames ME0 ⊆ T0 (sec:appendix-static-basis-modenv). -/"
               , "theorem tynames_ME0 : (ME0.flatMap fun p => p.2.tynames).all (fun t => decide (t ∈ T0)) = true := by"
               , "  decide +kernel"
               , ""
               , "/-- Step 8's list of the modules of the basis is the domain of ME0. -/"
               , "theorem basisModuleIds_eq : Src.basisModuleIds = ME0.keys := by decide +kernel"
               , ""
               , "end StandardElm.Stat"
               , ""
               ]
        )
