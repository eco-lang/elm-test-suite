module StaticBasis.Extract exposing (extract, summary)

{-| The extraction of Appendix C and of Figure fig:default-imports (plans/lean-full-definition/
step-07-classify.md, section 4), with its validations (4.4). Pure: the script reads the files.
-}

import Dict
import Set
import StaticBasis.Json exposing (Basis, DefaultImport, ExposedItem(..), Exposing(..), Interface, OperatorRow, TypeNameRow)
import StaticBasis.Latex as L exposing (TEntry, Token(..), Ty(..), VEntry)


type alias Sources =
    { appendix : String, syntaxModules : String, syntaxCore : String, shas : List ( String, String ) }


combine : List (Result String a) -> Result String (List a)
combine =
    List.foldr (Result.map2 (::)) (Ok [])


andThenAll : (a -> Result String (List b)) -> List a -> Result String (List b)
andThenAll f xs =
    xs |> List.map f |> combine |> Result.map List.concat


inFigure : String -> Result String a -> Result String a
inFigure fig =
    Result.mapError (\e -> fig ++ ": " ++ e)


{-| The rows of a figure, continuation rows joined.
-}
figureRows : String -> String -> Result String (List (List String))
figureRows label source =
    L.figureBody label source
        |> Result.map (L.arrayRows >> List.map L.cells >> L.joinContinuations)


typeNames : String -> Result String (List TypeNameRow)
typeNames appendix =
    figureRows "fig:static-basis-tynames" appendix
        |> Result.andThen
            (List.filter (\r -> List.head r /= Just "t")
                >> List.map
                    (\r ->
                        case r of
                            [ macroCell, arityCell, boundCell ] ->
                                case ( L.tokenize macroCell, String.toInt (String.trim arityCell) ) of
                                    ( Ok [ TyName m ], Just arity ) ->
                                        case L.typeNameOf m of
                                            Just ( key, a ) ->
                                                if a /= arity then
                                                    Err ("arity of \\" ++ m ++ " is " ++ String.fromInt arity ++ " in the figure")

                                                else
                                                    Ok
                                                        { key = key
                                                        , macro = m
                                                        , arity = arity
                                                        , boundTo = kwsIn boundCell
                                                        , kind = kindOf key
                                                        }

                                            Nothing ->
                                                Err ("unknown type name \\" ++ m)

                                    _ ->
                                        Err ("a row of the type names figure: " ++ String.join " & " r)

                            _ ->
                                Err ("a row of the type names figure: " ++ String.join " & " r)
                    )
                >> combine
            )
        |> inFigure "fig:static-basis-tynames"


kindOf : String -> String
kindOf key =
    if List.member key [ "Int", "Float", "Char", "String", "Unit", "List", "Tuple2", "Tuple3" ] then
        "builtin"

    else if key == "Never" then
        "custom-closed"

    else if List.member key [ "Bool", "Order", "Maybe", "Result" ] then
        "custom"

    else
        "abstract"


{-| Every `\kw{...}` of a text.
-}
kwsIn : String -> List String
kwsIn text =
    String.split "\\kw{" text
        |> List.drop 1
        |> List.filterMap (String.split "}" >> List.head)


{-| Dom ME0, from the display after "has the domain".
-}
domME0 : String -> Result String (List String)
domME0 appendix =
    case String.indexes "has the domain" appendix of
        at :: _ ->
            let
                rest =
                    String.dropLeft at appendix
            in
            case String.indexes "\\end{array}" rest of
                e :: _ ->
                    Ok (kwsIn (String.left e rest))

                [] ->
                    Err "Dom ME0: no \\end{array}"

        [] ->
            Err "Dom ME0: the display was not found"


{-| E0: the VE_0 display, and TE_0 = { List ↦ (List, VE_0) }.
-}
e0 : String -> Result String { te : List TEntry, ve : List VEntry }
e0 appendix =
    case String.indexes "\\VE_0 = \\{" appendix of
        at :: _ ->
            let
                text =
                    String.dropLeft (at + String.length "\\VE_0 = ") appendix
            in
            L.tokenize (takeUntilDisplayEnd text)
                |> Result.andThen L.parseVeEntries
                |> Result.andThen
                    (\( ve, rest ) ->
                        if rest == [ Dot ] || rest == [] then
                            Ok ve

                        else
                            Err "VE_0: left over"
                    )
                |> Result.andThen
                    (\ve ->
                        case String.indexes "\\TE_0 = \\{" appendix of
                            t :: _ ->
                                let
                                    teText =
                                        String.dropLeft (t + String.length "\\TE_0 = ") appendix |> takeUntil "\\}" |> (\s -> s ++ "\\}")
                                in
                                case L.tokenize teText of
                                    Ok [ LBrace, Kw "List", Label l, Mapsto, LParen, TyName "tList", Comma, VE0, RParen, RBrace ] ->
                                        Ok { te = [ { tycon = "List", labels = [ l ], typeName = "List", ve = ve } ], ve = ve }

                                    Ok _ ->
                                        Err "TE_0 is not { List ↦ (List, VE_0) }"

                                    Err e ->
                                        Err ("TE_0: " ++ e)

                            [] ->
                                Err "TE_0 display not found"
                    )
                |> inFigure "E0"

        [] ->
            Err "the VE_0 display was not found"


takeUntil : String -> String -> String
takeUntil marker s =
    case String.indexes marker s of
        i :: _ ->
            String.left i s

        [] ->
            s


takeUntilDisplayEnd : String -> String
takeUntilDisplayEnd s =
    takeUntil "\\]" s


{-| The rows of a three-column interface figure: the module headings, TE rows and VE rows.
`fixed` is the module of the Basics figures, which have no headings.
-}
type RowItem
    = TeItem TEntry
    | VeItem (List VEntry)


interfaceRows : Maybe String -> String -> String -> Result String (List ( List String, RowItem ))
interfaceRows fixed label appendix =
    figureRows label appendix
        |> Result.andThen
            (\rows ->
                let
                    step row ( current, acc ) =
                        case acc of
                            Err e ->
                                ( current, Err e )

                            Ok done ->
                                case row of
                                    [ single ] ->
                                        if String.startsWith "\\multicolumn" single then
                                            ( kwsIn single, Ok done )

                                        else
                                            ( current, Err ("a one-cell row: " ++ single) )

                                    [ first, mid, third ] ->
                                        if String.contains "\\tycon" first || String.contains "\\var" first then
                                            ( current, Ok done )

                                        else if String.trim mid /= "\\mapsto" then
                                            ( current, Err ("a row without \\mapsto: " ++ String.join " & " row) )

                                        else if String.endsWith "\\isc)" (String.trim third) || String.endsWith "\\isv)" (String.trim third) then
                                            ( current, L.parseVeRow first third |> Result.map (\ve -> done ++ [ ( current, VeItem ve ) ]) )

                                        else
                                            ( current, L.parseTeRow first third |> Result.map (\te -> done ++ [ ( current, TeItem te ) ]) )

                                    _ ->
                                        ( current, Err ("a row of " ++ String.fromInt (List.length row) ++ " cells") )
                in
                List.foldl step ( fixed |> Maybe.map List.singleton |> Maybe.withDefault [], Ok [] ) rows |> Tuple.second
            )
        |> inFigure label


operators : String -> Result String (List OperatorRow)
operators appendix =
    figureRows "fig:static-basis-operators" appendix
        |> Result.andThen
            (List.filter (\r -> not (List.any (String.contains "\\opv") r))
                >> List.map
                    (\r ->
                        case r of
                            [ ops, names, mid, third ] ->
                                if String.trim mid /= "\\mapsto" then
                                    Err ("an operator row without \\mapsto: " ++ String.join " & " r)

                                else
                                    L.parseOpRow ops names third

                            _ ->
                                Err ("an operator row of " ++ String.fromInt (List.length r) ++ " cells")
                    )
                >> combine
                >> Result.map List.concat
            )
        |> Result.map
            (List.indexedMap
                (\i ( op, e, starred ) ->
                    { op = op
                    , rank = i + 1
                    , standsFor = e.name
                    , declaredBy =
                        if starred then
                            "List"

                        else
                            "Basics"
                    , label = e.labels |> List.filter (\l -> l /= "*") |> List.head
                    , scheme = e.scheme
                    , status = e.status
                    }
                )
            )
        |> inFigure "fig:static-basis-operators"


fixityOperators : String -> Result String (List String)
fixityOperators syntaxCore =
    figureRows "fig:core-fixities" syntaxCore
        |> Result.andThen
            (List.drop 1
                >> List.concatMap (List.drop 1)
                >> List.map
                    (\c ->
                        L.tokenize c
                            |> Result.map
                                (List.filterMap
                                    (\t ->
                                        case t of
                                            Kw k ->
                                                Just k

                                            _ ->
                                                Nothing
                                    )
                                )
                    )
                >> combine
                >> Result.map List.concat
            )
        |> inFigure "fig:core-fixities"


defaultImports : String -> Result String (List DefaultImport)
defaultImports syntaxModules =
    figureRows "fig:default-imports" syntaxModules
        |> Result.andThen
            (List.map
                (\r ->
                    case kwsIn (String.join " " r) |> List.map (String.replace "{}" "") of
                        [ text ] ->
                            parseImport (String.trim text)

                        _ ->
                            Err ("a default import row: " ++ String.join " " r)
                )
                >> combine
            )
        |> inFigure "fig:default-imports"


{-| `import M [as A] [exposing (...)]`, as the figure writes it.
-}
parseImport : String -> Result String DefaultImport
parseImport text =
    case String.words text of
        "import" :: m :: rest ->
            let
                ( as_, rest2 ) =
                    case rest of
                        "as" :: a :: r ->
                            ( Just a, r )

                        _ ->
                            ( Nothing, rest )
            in
            case rest2 of
                [] ->
                    Ok { module_ = m, as_ = as_, exposing_ = Nothing }

                "exposing" :: _ ->
                    let
                        inner =
                            text |> String.split "exposing" |> List.drop 1 |> String.join "exposing" |> String.trim |> String.dropLeft 1 |> String.dropRight 1
                    in
                    if inner == ".." then
                        Ok { module_ = m, as_ = as_, exposing_ = Just ExposingAll }

                    else
                        inner
                            |> String.split ","
                            |> List.map String.trim
                            |> List.map
                                (\it ->
                                    if String.startsWith "(" it then
                                        Ok (ExpOp (it |> String.dropLeft 1 |> String.dropRight 1))

                                    else if String.endsWith "(..)" it then
                                        Ok (ExpTypeAll (String.dropRight 4 it))

                                    else if Maybe.map Char.isUpper (String.uncons it |> Maybe.map Tuple.first) == Just True then
                                        Ok (ExpType it)

                                    else
                                        Ok (ExpValue it)
                                )
                            |> combine
                            |> Result.map (\items -> { module_ = m, as_ = as_, exposing_ = Just (ExposingItems items) })

                _ ->
                    Err ("an import: " ++ text)

        _ ->
            Err ("an import: " ++ text)


libraryOf : String -> String
libraryOf m =
    case m of
        "Bytes" ->
            "elm/bytes"

        "Json.Encode" ->
            "elm/json"

        "Json.Decode" ->
            "elm/json"

        "VirtualDom" ->
            "elm/virtual-dom"

        "Html" ->
            "elm/html"

        _ ->
            "elm/core"


{-| The extraction, validated.
-}
extract : Sources -> Result String Basis
extract src =
    let
        figures =
            [ ( Just "Basics", "fig:static-basis-basics-te" )
            , ( Just "Basics", "fig:static-basis-basics-ve1" )
            , ( Just "Basics", "fig:static-basis-basics-ve2" )
            , ( Nothing, "fig:static-basis-data" )
            , ( Nothing, "fig:static-basis-platform" )
            , ( Nothing, "fig:static-basis-task" )
            , ( Nothing, "fig:static-basis-effects" )
            ]
    in
    Result.map5
        (\tn dom e ops imports -> ( ( tn, dom, e ), ops, imports ))
        (typeNames src.appendix)
        (domME0 src.appendix)
        (e0 src.appendix)
        (operators src.appendix)
        (defaultImports src.syntaxModules)
        |> Result.andThen
            (\( ( tn, dom, e ), ops, imports ) ->
                figures
                    |> List.map (\( fixed, label ) -> interfaceRows (Maybe.map identity fixed) label src.appendix)
                    |> combine
                    |> Result.map List.concat
                    |> Result.andThen
                        (\rows ->
                            let
                                interfaceOf m =
                                    { module_ = m
                                    , library = libraryOf m
                                    , te = teOf m rows
                                    , ve = veOf m rows
                                    , ops =
                                        ops
                                            |> List.filter (\o -> o.declaredBy == m)
                                            |> List.map .op
                                    }

                                modules =
                                    List.map interfaceOf dom

                                hidden =
                                    closedHidden modules
                                        ++ taskHidden src.appendix
                            in
                            validate tn dom modules ops imports src
                                |> Result.map
                                    (\_ ->
                                        { sources = src.shas
                                        , typeNames = tn
                                        , e0 = e
                                        , modules = modules
                                        , operators = ops
                                        , hidden = hidden
                                        , defaultImports = imports
                                        }
                                    )
                        )
            )


teOf : String -> List ( List String, RowItem ) -> List TEntry
teOf m rows =
    rows
        |> List.filterMap
            (\( ms, r ) ->
                case r of
                    TeItem te ->
                        if List.member m ms then
                            Just te

                        else
                            Nothing

                    VeItem _ ->
                        Nothing
            )


veOf : String -> List ( List String, RowItem ) -> List VEntry
veOf m rows =
    rows
        |> List.concatMap
            (\( ms, r ) ->
                case r of
                    VeItem ve ->
                        if List.member m ms then
                            ve

                        else
                            []

                    TeItem _ ->
                        []
            )


{-| The constructors of a closed type: in its type structure, absent from the module's VE.
-}
closedHidden : List Interface -> List { module_ : String, name : String, kind : String, typeName : Maybe String, note : Maybe String }
closedHidden modules =
    modules
        |> List.concatMap
            (\i ->
                i.te
                    |> List.concatMap
                        (\te ->
                            te.ve
                                |> List.filter (\c -> not (List.any (\v -> v.name == c.name) i.ve))
                                |> List.map (\c -> { module_ = i.module_, name = c.name, kind = "constructor", typeName = Just te.typeName, note = Nothing })
                        )
            )


{-| The hidden identifiers of Task, from the paragraph "Hidden identifiers" (checked to name them).
-}
taskHidden : String -> List { module_ : String, name : String, kind : String, typeName : Maybe String, note : Maybe String }
taskHidden appendix =
    let
        para =
            String.split "\\textbf{Hidden identifiers.}" appendix |> List.drop 1 |> List.head |> Maybe.withDefault "" |> takeUntil "\\textbf{"
    in
    (if String.contains "\\kw{Perform}" para && String.contains "\\kw{MyCmd}" para then
        [ { module_ = "Task", name = "Perform", kind = "constructor", typeName = Nothing, note = Just "type MyCmd msg = Perform (Task Never msg); MyCmd is not in T0" } ]

     else
        []
    )
        ++ (if String.contains "\\kw{command}" para then
                [ { module_ = "Task", name = "command", kind = "value", typeName = Nothing, note = Nothing } ]

            else
                []
           )


tyNames : Ty -> List String
tyNames t =
    case t of
        TyVar _ ->
            []

        TyCon c args ->
            c :: List.concatMap tyNames args

        TyFn a b ->
            tyNames a ++ tyNames b

        TyRecord fs ->
            List.concatMap (Tuple.second >> tyNames) fs


validate : List TypeNameRow -> List String -> List Interface -> List OperatorRow -> List DefaultImport -> Sources -> Result String ()
validate tn dom modules ops imports src =
    let
        keys =
            Set.fromList (List.map .key tn)

        used =
            modules
                |> List.concatMap (\i -> List.concatMap (.scheme >> .body >> tyNames) i.ve ++ List.map .typeName i.te)
                |> Set.fromList

        withRows =
            modules |> List.filter (\i -> not (List.isEmpty i.te && List.isEmpty i.ve)) |> List.map .module_

        fixity =
            fixityOperators src.syntaxCore |> Result.withDefault []

        problems =
            (if Set.isEmpty (Set.diff used keys) then
                []

             else
                [ "tynames ME0 ⊄ T0: " ++ String.join ", " (Set.toList (Set.diff used keys)) ]
            )
                ++ (if Set.fromList dom == Set.fromList (withRows ++ [ "List", "Tuple" ]) then
                        []

                    else
                        [ "Dom ME0 differs from the modules with rows, List and Tuple" ]
                   )
                ++ (if Set.fromList fixity == Set.fromList (List.map .op ops) && List.length fixity == 20 then
                        []

                    else
                        [ "the operators of fig:core-fixities and fig:static-basis-operators differ" ]
                   )
                ++ List.concatMap (importProblems dom modules ops) imports
                ++ (modules
                        |> List.concatMap
                            (\i ->
                                i.te
                                    |> List.filter (\te -> te.typeName /= "Never")
                                    |> List.concatMap
                                        (\te ->
                                            te.ve
                                                |> List.filter (\c -> not (List.any (\v -> v.name == c.name && v.scheme == c.scheme) i.ve))
                                                |> List.map (\c -> i.module_ ++ "." ++ c.name ++ ": a constructor of an open type absent from the interface")
                                        )
                            )
                   )
    in
    if List.isEmpty problems then
        Ok ()

    else
        Err (String.join "\n" problems)


importProblems : List String -> List Interface -> List OperatorRow -> DefaultImport -> List String
importProblems dom modules ops imp =
    if not (List.member imp.module_ dom) then
        [ "default import of a module outside Dom ME0: " ++ imp.module_ ]

    else
        case imp.exposing_ of
            Just (ExposingItems items) ->
                let
                    iface =
                        modules |> List.filter (\i -> i.module_ == imp.module_) |> List.head
                in
                items
                    |> List.filterMap
                        (\it ->
                            case ( it, iface ) of
                                ( ExpOp o, _ ) ->
                                    if List.any (\r -> r.op == o && r.declaredBy == imp.module_) ops then
                                        Nothing

                                    else
                                        Just ("default import exposes an operator its module does not declare: " ++ o)

                                ( ExpType t, Just i ) ->
                                    if List.any (\te -> te.tycon == t) i.te then
                                        Nothing

                                    else
                                        Just ("default import exposes a type absent from " ++ imp.module_ ++ ": " ++ t)

                                ( ExpTypeAll t, Just i ) ->
                                    if List.any (\te -> te.tycon == t) i.te then
                                        Nothing

                                    else
                                        Just ("default import exposes a type absent from " ++ imp.module_ ++ ": " ++ t)

                                ( ExpValue x, Just i ) ->
                                    if List.any (\v -> v.name == x) i.ve then
                                        Nothing

                                    else
                                        Just ("default import exposes a value absent from " ++ imp.module_ ++ ": " ++ x)

                                ( _, Nothing ) ->
                                    Just ("no interface for " ++ imp.module_)
                        )

            _ ->
                []


summary : Basis -> String
summary b =
    "static basis: "
        ++ String.fromInt (List.length b.typeNames)
        ++ " type names, "
        ++ String.fromInt (List.length b.modules)
        ++ " modules, "
        ++ String.fromInt (List.length b.operators)
        ++ " operators, "
        ++ String.fromInt (List.length b.hidden)
        ++ " hidden identifiers, "
        ++ String.fromInt (List.length b.defaultImports)
        ++ " default imports"
