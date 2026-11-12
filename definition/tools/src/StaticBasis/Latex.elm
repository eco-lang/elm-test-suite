module StaticBasis.Latex exposing
    ( Scheme
    , TEntry
    , Ty(..)
    , VEntry
    , arrayRows
    , cells
    , figureBody
    , joinContinuations
    , kwNames
    , parseOpRow
    , parseTeRow
    , parseVeRow
    , parseVeEntries
    , tokenize
    , Token(..)
    , typeNameOf
    )

{-| Reading Appendix C of A Standard Definition of Elm? (plans/lean-full-definition/step-07-classify.md,
section 4): tokenising a LaTeX array, joining continuation rows, and parsing type schemes, value
environment rows, type environment rows and operator rows. Every function fails, with a message
naming what it met, on anything it does not recognise; it never guesses.
-}


{-| A type: a variable by its spelling (its class follows from the spelling, A19), a type name
(a key of the type names figure) applied to arguments, a function type, a closed record.
-}
type Ty
    = TyVar String
    | TyCon String (List Ty)
    | TyFn Ty Ty
    | TyRecord (List ( String, Ty ))


type alias Scheme =
    { forall : List String, body : Ty }


{-| A value environment entry: the name, its labels, the scheme and the status ("c" or "v").
-}
type alias VEntry =
    { name : String, labels : List String, scheme : Scheme, status : String }


{-| A type environment entry: the type constructor, its labels, the type name it is bound to, and
the value environment of its type structure.
-}
type alias TEntry =
    { tycon : String, labels : List String, typeName : String, ve : List VEntry }



-- TYPE NAMES


{-| The key and arity of a type-name macro (Figure fig:static-basis-tynames).
-}
typeNameOf : String -> Maybe ( String, Int )
typeNameOf macroName =
    case macroName of
        "tInt" ->
            Just ( "Int", 0 )

        "tFloat" ->
            Just ( "Float", 0 )

        "tChar" ->
            Just ( "Char", 0 )

        "tString" ->
            Just ( "String", 0 )

        "tunit" ->
            Just ( "Unit", 0 )

        "tList" ->
            Just ( "List", 1 )

        "tTuple{2}" ->
            Just ( "Tuple2", 2 )

        "tTuple{3}" ->
            Just ( "Tuple3", 3 )

        "tBool" ->
            Just ( "Bool", 0 )

        "sbtOrder" ->
            Just ( "Order", 0 )

        "sbtNever" ->
            Just ( "Never", 0 )

        "tMaybe" ->
            Just ( "Maybe", 1 )

        "sbtResult" ->
            Just ( "Result", 2 )

        "tArray" ->
            Just ( "Array", 1 )

        "tBytes" ->
            Just ( "Bytes", 0 )

        "tValue" ->
            Just ( "Value", 0 )

        "sbtCmd" ->
            Just ( "Cmd", 1 )

        "sbtSub" ->
            Just ( "Sub", 1 )

        "sbtTask" ->
            Just ( "Task", 2 )

        "sbtProcessId" ->
            Just ( "ProcessId", 0 )

        "sbtProgram" ->
            Just ( "Program", 3 )

        "sbtNode" ->
            Just ( "Node", 1 )

        _ ->
            Nothing



-- LOCATING FIGURES AND ROWS


{-| The text of the array or tabular of the figure (or display) whose `\label` is the given one:
from the last `\begin{array}` or `\begin{tabular}` before the label to its `\end`.
-}
figureBody : String -> String -> Result String String
figureBody label source =
    case String.indexes ("\\label{" ++ label ++ "}") source of
        at :: _ ->
            let
                before =
                    String.left at source

                begins =
                    List.map (\i -> ( i, "array" )) (String.indexes "\\begin{array}" before)
                        ++ List.map (\i -> ( i, "tabular" )) (String.indexes "\\begin{tabular}" before)
            in
            case List.reverse (List.sortBy Tuple.first begins) of
                ( b, env ) :: _ ->
                    let
                        rest =
                            String.dropLeft b before
                    in
                    case String.indexes ("\\end{" ++ env ++ "}") rest of
                        e :: _ ->
                            Ok (String.left e rest |> dropEnvHeader env)

                        [] ->
                            Err (label ++ ": no \\end{" ++ env ++ "}")

                [] ->
                    Err (label ++ ": no array or tabular before the label")

        [] ->
            Err ("no label " ++ label)


{-| Drop `\begin{array}{...}` and its column specification (balanced braces).
-}
dropEnvHeader : String -> String -> String
dropEnvHeader env s =
    let
        afterBegin =
            String.dropLeft (String.length ("\\begin{" ++ env ++ "}")) s
    in
    case String.uncons afterBegin of
        Just ( '{', _ ) ->
            dropBalanced afterBegin

        _ ->
            afterBegin


{-| Drop a leading balanced brace group.
-}
dropBalanced : String -> String
dropBalanced s =
    let
        go depth cs =
            case cs of
                '\\' :: '{' :: rest ->
                    go depth rest

                '\\' :: '}' :: rest ->
                    go depth rest

                '{' :: rest ->
                    go (depth + 1) rest

                '}' :: rest ->
                    if depth == 1 then
                        rest

                    else
                        go (depth - 1) rest

                _ :: rest ->
                    go depth rest

                [] ->
                    []
    in
    String.fromList (go 0 (String.toList s))


{-| The rows of an array body: split at `\\`, `\hline` removed, blank rows dropped.
-}
arrayRows : String -> List String
arrayRows body =
    body
        |> String.split "\\\\"
        |> List.map (String.replace "\\hline" "" >> String.trim)
        |> List.filter (not << String.isEmpty)


{-| The cells of a row: split at `&`, but not at `\&`.
-}
cells : String -> List String
cells row =
    let
        go cs cur acc =
            case cs of
                '\\' :: '&' :: rest ->
                    go rest ('&' :: '\\' :: cur) acc

                '&' :: rest ->
                    go rest [] (String.fromList (List.reverse cur) :: acc)

                c :: rest ->
                    go rest (c :: cur) acc

                [] ->
                    List.reverse (String.fromList (List.reverse cur) :: acc)
    in
    go (String.toList row) [] [] |> List.map String.trim


{-| Join continuation rows: a row whose cells but the last are empty is appended to the last cell
of the row before it.
-}
joinContinuations : List (List String) -> List (List String)
joinContinuations rows =
    let
        isCont r =
            case List.reverse r of
                _ :: firsts ->
                    not (List.isEmpty firsts) && List.all String.isEmpty firsts

                [] ->
                    False

        step r acc =
            if isCont r then
                case acc of
                    prev :: rest ->
                        let
                            n =
                                List.length prev
                        in
                        (List.take (n - 1) prev ++ [ String.join " " (List.drop (n - 1) prev ++ List.drop (n - 1) r) ]) :: rest

                    [] ->
                        acc

            else
                r :: acc
    in
    List.foldl step [] rows |> List.reverse



-- TOKENS


type Token
    = LParen
    | RParen
    | Comma
    | Dot
    | LBrace
    | RBrace
    | Forall
    | Arrow
    | Mapsto
    | Mv String
    | Kw String
    | Label String
    | TyName String
    | Isc
    | Isv
    | Emptymap
    | VE0
    | Star


{-| Tokenise a cell. Layout (`\phantom{...}`, `\quad`, `\,`, `\ `, `{}`, `\allowbreak`) is dropped.
-}
tokenize : String -> Result String (List Token)
tokenize s =
    tok (String.toList s) []


tok : List Char -> List Token -> Result String (List Token)
tok cs acc =
    case cs of
        [] ->
            Ok (List.reverse acc)

        c :: rest ->
            if c == ' ' || c == '\n' || c == '\t' then
                tok rest acc

            else
                case cs of
                    '{' :: '}' :: r ->
                        tok r acc

                    '(' :: r ->
                        tok r (LParen :: acc)

                    ')' :: r ->
                        tok r (RParen :: acc)

                    ',' :: r ->
                        tok r (Comma :: acc)

                    '.' :: r ->
                        tok r (Dot :: acc)

                    '^' :: '{' :: '*' :: '}' :: r ->
                        tok r (Star :: acc)

                    '\\' :: '{' :: r ->
                        tok r (LBrace :: acc)

                    '\\' :: '}' :: r ->
                        tok r (RBrace :: acc)

                    '\\' :: ',' :: r ->
                        tok r acc

                    '\\' :: ' ' :: r ->
                        tok r acc

                    '\\' :: '\n' :: r ->
                        tok r acc

                    '\\' :: r ->
                        let
                            ( name, r2 ) =
                                spanLetters r
                        in
                        macro name r2 acc

                    _ ->
                        Err ("unexpected character " ++ String.fromChar c ++ " in " ++ String.fromList (List.take 40 cs))


macro : String -> List Char -> List Token -> Result String (List Token)
macro name r acc =
    case name of
        "phantom" ->
            tok (String.toList (dropBalanced (String.fromList r))) acc

        "quad" ->
            tok r acc

        "allowbreak" ->
            tok r acc

        "forall" ->
            tok r (Forall :: acc)

        "rightarrow" ->
            tok r (Arrow :: acc)

        "mapsto" ->
            tok r (Mapsto :: acc)

        "isc" ->
            tok r (Isc :: acc)

        "isv" ->
            tok r (Isv :: acc)

        "emptymap" ->
            tok r (Emptymap :: acc)

        "VE" ->
            case r of
                '_' :: '0' :: r2 ->
                    tok r2 (VE0 :: acc)

                _ ->
                    Err "\\VE without _0"

        "mv" ->
            arg r |> Result.andThen (\( a, r2 ) -> tok r2 (Mv a :: acc))

        "kw" ->
            arg r |> Result.andThen (\( a, r2 ) -> tok r2 (Kw (kwText a) :: acc))

        "citelabel" ->
            arg r |> Result.andThen (\( a, r2 ) -> tok r2 (Label a :: acc))

        "citealso" ->
            arg r |> Result.andThen (\( a, r2 ) -> tok r2 (Label a :: acc))

        "tTuple" ->
            arg r |> Result.andThen (\( a, r2 ) -> tok r2 (TyName ("tTuple{" ++ a ++ "}") :: acc))

        _ ->
            case typeNameOf name of
                Just _ ->
                    tok r (TyName name :: acc)

                Nothing ->
                    Err ("unknown macro \\" ++ name)


{-| The text of `\kw{...}`: `{}` removed, `\textasciicircum` is `^`, `\&` is `&`.
-}
kwText : String -> String
kwText a =
    a
        |> String.replace "{}" ""
        |> String.replace "\\textasciicircum" "^"
        |> String.replace "\\&" "&"


arg : List Char -> Result String ( String, List Char )
arg r =
    case r of
        '{' :: _ ->
            let
                s =
                    String.fromList r

                rest =
                    dropBalanced s

                inner =
                    String.slice 1 (String.length s - String.length rest - 1) s
            in
            Ok ( inner, String.toList rest )

        _ ->
            Err ("expected an argument in braces at " ++ String.fromList (List.take 30 r))


spanLetters : List Char -> ( String, List Char )
spanLetters cs =
    let
        go acc rest =
            case rest of
                c :: r ->
                    if Char.isAlpha c then
                        go (c :: acc) r

                    else
                        ( String.fromList (List.reverse acc), rest )

                [] ->
                    ( String.fromList (List.reverse acc), [] )
    in
    go [] cs



-- PARSERS


type alias P a =
    List Token -> Result String ( a, List Token )


expect : Token -> List Token -> Result String (List Token)
expect t ts =
    case ts of
        t2 :: rest ->
            if t2 == t then
                Ok rest

            else
                Err ("expected " ++ showTok t ++ ", found " ++ showTok t2)

        [] ->
            Err ("expected " ++ showTok t ++ ", found the end")


showTok : Token -> String
showTok t =
    case t of
        LParen ->
            "("

        RParen ->
            ")"

        Comma ->
            ","

        Dot ->
            "."

        LBrace ->
            "\\{"

        RBrace ->
            "\\}"

        Forall ->
            "\\forall"

        Arrow ->
            "\\rightarrow"

        Mapsto ->
            "\\mapsto"

        Mv a ->
            "\\mv{" ++ a ++ "}"

        Kw a ->
            "\\kw{" ++ a ++ "}"

        Label a ->
            "label " ++ a

        TyName a ->
            "\\" ++ a

        Isc ->
            "\\isc"

        Isv ->
            "\\isv"

        Emptymap ->
            "\\emptymap"

        VE0 ->
            "\\VE_0"

        Star ->
            "^{*}"


{-| scheme ::= "\forall" var+ "." type | type
-}
scheme : P Scheme
scheme ts =
    case ts of
        Forall :: rest ->
            let
                vars acc r =
                    case r of
                        (Mv a) :: r2 ->
                            vars (a :: acc) r2

                        Dot :: r2 ->
                            Ok ( List.reverse acc, r2 )

                        _ ->
                            Err "expected a variable or . after \\forall"
            in
            vars [] rest
                |> Result.andThen
                    (\( vs, r ) ->
                        ty r |> Result.map (\( t, r2 ) -> ( { forall = vs, body = t }, r2 ))
                    )

        _ ->
            ty ts |> Result.map (\( t, r ) -> ( { forall = [], body = t }, r ))


{-| type ::= app ("\rightarrow" type)?
-}
ty : P Ty
ty ts =
    app ts
        |> Result.andThen
            (\( a, r ) ->
                case r of
                    Arrow :: r2 ->
                        ty r2 |> Result.map (\( b, r3 ) -> ( TyFn a b, r3 ))

                    _ ->
                        Ok ( a, r )
            )


{-| app ::= atom tyname*, the arguments before the name.
-}
app : P Ty
app ts =
    atom ts |> Result.andThen (\( args, r ) -> postfix args r)


{-| The arguments an atom supplies: one type, or a parenthesised sequence of two or more.
-}
postfix : List Ty -> List Token -> Result String ( Ty, List Token )
postfix args ts =
    case ts of
        (TyName m) :: rest ->
            applyName m args |> Result.andThen (\t -> postfix [ t ] rest)

        _ ->
            case args of
                [ t ] ->
                    Ok ( t, ts )

                _ ->
                    Err "a parenthesised sequence of types not followed by a type name"


applyName : String -> List Ty -> Result String Ty
applyName m args =
    case typeNameOf m of
        Just ( key, arity ) ->
            if List.length args == arity then
                Ok (TyCon key args)

            else
                Err ("\\" ++ m ++ " has arity " ++ String.fromInt arity ++ ", given " ++ String.fromInt (List.length args))

        Nothing ->
            Err ("unknown type name \\" ++ m)


atom : P (List Ty)
atom ts =
    case ts of
        (Mv a) :: rest ->
            Ok ( [ TyVar a ], rest )

        (TyName m) :: rest ->
            applyName m [] |> Result.map (\t -> ( [ t ], rest ))

        LParen :: rest ->
            ty rest
                |> Result.andThen
                    (\( t, r ) ->
                        case r of
                            RParen :: r2 ->
                                Ok ( [ t ], r2 )

                            Comma :: r2 ->
                                tySeq [ t ] r2

                            _ ->
                                Err "expected ) or , in a type"
                    )

        LBrace :: rest ->
            fields [] rest |> Result.map (\( fs, r ) -> ( [ TyRecord fs ], r ))

        t :: _ ->
            Err ("unexpected " ++ showTok t ++ " in a type")

        [] ->
            Err "a type expected, the end found"


tySeq : List Ty -> List Token -> Result String ( List Ty, List Token )
tySeq acc ts =
    ty ts
        |> Result.andThen
            (\( t, r ) ->
                case r of
                    Comma :: r2 ->
                        tySeq (acc ++ [ t ]) r2

                    RParen :: r2 ->
                        Ok ( acc ++ [ t ], r2 )

                    _ ->
                        Err "expected , or ) in a sequence of types"
            )


fields : List ( String, Ty ) -> List Token -> Result String ( List ( String, Ty ), List Token )
fields acc ts =
    case ts of
        (Kw l) :: Mapsto :: rest ->
            ty rest
                |> Result.andThen
                    (\( t, r ) ->
                        case r of
                            Comma :: r2 ->
                                fields (acc ++ [ ( l, t ) ]) r2

                            RBrace :: r2 ->
                                Ok ( acc ++ [ ( l, t ) ], r2 )

                            _ ->
                                Err "expected , or \\} in a record type"
                    )

        _ ->
            Err "expected a field of a record type"


{-| ( scheme , status )
-}
pair : P ( Scheme, String )
pair ts =
    expect LParen ts
        |> Result.andThen scheme
        |> Result.andThen
            (\( s, r ) ->
                expect Comma r
                    |> Result.andThen
                        (\r2 ->
                            case r2 of
                                Isc :: RParen :: r3 ->
                                    Ok ( ( s, "c" ), r3 )

                                Isv :: RParen :: r3 ->
                                    Ok ( ( s, "v" ), r3 )

                                _ ->
                                    Err "expected \\isc) or \\isv)"
                        )
            )


{-| The names of a first cell: `\kw{a}\citelabel{..}, \kw{b}...`, with their labels.
-}
kwNames : List Token -> Result String (List ( String, List String ))
kwNames ts =
    let
        go acc cur rest =
            case rest of
                (Kw a) :: r ->
                    case cur of
                        Just c ->
                            go (acc ++ [ c ]) (Just ( a, [] )) r

                        Nothing ->
                            go acc (Just ( a, [] )) r

                (Label l) :: r ->
                    case cur of
                        Just ( a, ls ) ->
                            go acc (Just ( a, ls ++ [ l ] )) r

                        Nothing ->
                            Err "a label before any name"

                Comma :: r ->
                    go acc cur r

                Star :: r ->
                    case cur of
                        Just ( a, ls ) ->
                            go acc (Just ( a, ls ++ [ "*" ] )) r

                        Nothing ->
                            Err "^{*} before any name"

                [] ->
                    Ok (acc ++ (cur |> Maybe.map List.singleton |> Maybe.withDefault []))

                t :: _ ->
                    Err ("unexpected " ++ showTok t ++ " among names")
    in
    go [] Nothing ts


finish : ( a, List Token ) -> Result String a
finish ( a, rest ) =
    if List.isEmpty rest then
        Ok a

    else
        Err ("left over: " ++ String.join " " (List.map showTok (List.take 6 rest)))


{-| A VE row (simple, multi-name, joined): every name gets the scheme and status.
-}
parseVeRow : String -> String -> Result String (List VEntry)
parseVeRow first third =
    Result.map2
        (\names ( s, st ) -> List.map (\( n, ls ) -> { name = n, labels = ls, scheme = s, status = st }) names)
        (tokenize first |> Result.andThen kwNames)
        (tokenize third |> Result.andThen pair |> Result.andThen finish)


{-| A brace list of VE entries `\{ \kw{x} \mapsto (σ, is), ... \}`, or `\emptymap`.
-}
parseVeEntries : List Token -> Result String ( List VEntry, List Token )
parseVeEntries ts =
    case ts of
        Emptymap :: rest ->
            Ok ( [], rest )

        LBrace :: rest ->
            let
                go acc r =
                    case r of
                        (Kw n) :: r2 ->
                            let
                                ( labels, r3 ) =
                                    takeLabels [] r2
                            in
                            expect Mapsto r3
                                |> Result.andThen pair
                                |> Result.andThen
                                    (\( ( s, st ), r4 ) ->
                                        let
                                            e =
                                                { name = n, labels = labels, scheme = s, status = st }
                                        in
                                        case r4 of
                                            Comma :: r5 ->
                                                go (acc ++ [ e ]) r5

                                            RBrace :: r5 ->
                                                Ok ( acc ++ [ e ], r5 )

                                            _ ->
                                                Err "expected , or \\} after an entry"
                                    )

                        _ ->
                            Err "expected an entry"
            in
            go [] rest

        _ ->
            Err "expected \\emptymap or \\{"


takeLabels : List String -> List Token -> ( List String, List Token )
takeLabels acc ts =
    case ts of
        (Label l) :: r ->
            takeLabels (acc ++ [ l ]) r

        _ ->
            ( acc, ts )


{-| A TE row: `\kw{T}\citelabel{..} & \mapsto & (θ, VE)`.
-}
parseTeRow : String -> String -> Result String TEntry
parseTeRow first third =
    tokenize first
        |> Result.andThen kwNames
        |> Result.andThen
            (\names ->
                case names of
                    [ ( n, ls ) ] ->
                        tokenize third
                            |> Result.andThen
                                (\ts ->
                                    case ts of
                                        LParen :: (TyName m) :: Comma :: rest ->
                                            case typeNameOf m of
                                                Just ( key, _ ) ->
                                                    parseVeEntries rest
                                                        |> Result.andThen
                                                            (\( ve, r ) ->
                                                                expect RParen r
                                                                    |> Result.andThen
                                                                        (\r2 -> finish ( { tycon = n, labels = ls, typeName = key, ve = ve }, r2 ))
                                                            )

                                                Nothing ->
                                                    Err ("unknown type name \\" ++ m)

                                        _ ->
                                            Err "a TE row's third cell is (θ, VE)"
                                )

                    _ ->
                        Err "a TE row names one type constructor"
            )


{-| An operator row: operators, the names they stand for (paired in order), and the pair.
-}
parseOpRow : String -> String -> String -> Result String (List ( String, VEntry, Bool ))
parseOpRow opsCell namesCell third =
    Result.map3
        (\ops names ( s, st ) ->
            List.map2
                (\( op, flags ) ( n, ls ) ->
                    ( op, { name = n, labels = ls, scheme = s, status = st }, List.member "*" flags )
                )
                ops
                names
        )
        (tokenize opsCell |> Result.andThen kwNames)
        (tokenize namesCell |> Result.andThen kwNames)
        (tokenize third |> Result.andThen pair |> Result.andThen finish)
        |> Result.andThen
            (\rows ->
                case ( tokenize opsCell |> Result.andThen kwNames, tokenize namesCell |> Result.andThen kwNames ) of
                    ( Ok a, Ok b ) ->
                        if List.length a == List.length b then
                            Ok rows

                        else
                            Err "an operator row pairs lists of unequal length"

                    _ ->
                        Ok rows
            )
