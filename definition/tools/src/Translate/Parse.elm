module Translate.Parse exposing
    ( Function
    , Import
    , Parsed
    , c1
    , c2
    , c2eol
    , charValue
    , declarations
    , describe
    , exposing_
    , functions
    , headerRegion
    , importsOf
    , isPortModule
    , moduleName
    , parse
    , recordPatternFields
    , recordType
    , stringValue
    )

{-| The translator's one entry to eco's parser (plans/eco-parser.md, E4): a module's text to eco's
tree, its comments dropped where they wrap the module's parts, or to a short description of where
and why the text does not parse.

The tree below the declarations is eco's own (`Compiler.IR.Source`), comment wrappers included;
`c1`, `c2` and `c2eol` take a value out of them. eco keeps the fields of a record pattern in
reverse source order; `recordPatternFields` gives them in source order (E9), and every reader of a
record pattern reads them through it.

-}

import Compiler.Core.Annotation as A
import Compiler.IR.Source as Src
import Compiler.IR.Source.StringLiteral as StringLiteral
import Compiler.Lexer.Primitives as P
import Compiler.Parse.Declaration as Decl
import Compiler.Parse.Error as E
import Compiler.Parse.Module as Module
import Translate.Region as Region exposing (Region)


{-| A parsed module: eco's header (name, exposing, port flag, regions), the imports in source
order, the `infix` declarations, and the declarations in source order.
-}
type alias Parsed =
    { header : Maybe Module.Header
    , imports : List Src.Import
    , infixes : List (A.Located Src.Infix)
    , decls : List Decl.Decl
    }


{-| Parses a whole module.
-}
parse : String -> Result String Parsed
parse source =
    case P.fromByteString Module.chompModule E.ModuleBadEnd source of
        Ok m ->
            Ok
                { header = m.header
                , imports = List.map c1 (c1 m.imports)
                , infixes = List.reverse (List.map c1 m.infixes)
                , decls = List.map c2 m.decls
                }

        Err e ->
            Err (describe e)


c1 : Src.C1 a -> a
c1 =
    Tuple.second


c2 : Src.C2 a -> a
c2 =
    Tuple.second


c2eol : Src.C2Eol a -> a
c2eol =
    Tuple.second



-- THE HEADER


{-| The module's name, `Nothing` for a module without a header.
-}
moduleName : Parsed -> Maybe String
moduleName p =
    p.header |> Maybe.map (\h -> A.toValue (c2 h.name))


{-| What the header exposes; `exposing (..)` for a module without a header.
-}
exposing_ : Parsed -> Src.Exposing
exposing_ p =
    case p.header of
        Just h ->
            A.toValue (c2 h.exports)

        Nothing ->
            Src.Open [] []


isPortModule : Parsed -> Bool
isPortModule p =
    case p.header |> Maybe.map .effects of
        Just (Module.Ports _ _) ->
            True

        _ ->
            False


{-| The region of the header's keywords, from `module` (or `port`) to the end of `module`; the
start of the file for a module without a header.
-}
headerRegion : Parsed -> Region
headerRegion p =
    case p.header |> Maybe.map .effects of
        Just (Module.NoEffects r) ->
            Region.fromA r

        Just (Module.Ports r _) ->
            Region.fromA r

        Just (Module.Manager r _ _) ->
            Region.fromA r

        Nothing ->
            { start = { row = 1, column = 1 }, end = { row = 1, column = 1 } }



-- IMPORTS AND DECLARATIONS


{-| One import as written: the module's name, its alias, its exposing list (`Nothing` when it has
none) and the row of the module's name. eco's import has no region of its own; an import starts
its line, so `{ row = row, column = 1 }` is where it starts (E10).
-}
type alias Import =
    { name : String, alias : Maybe String, exposing_ : Maybe Src.Exposing, row : Int }


importsOf : Parsed -> List Import
importsOf p =
    List.map
        (\(Src.Import ( _, A.At (A.Region (A.Position row _) _) name ) alias ( _, ex )) ->
            { name = name
            , alias = Maybe.map c2 alias
            , exposing_ =
                case ex of
                    Src.Explicit (A.At _ []) ->
                        Nothing

                    _ ->
                        Just ex
            , row = row
            }
        )
        p.imports


declarations : Parsed -> List Decl.Decl
declarations p =
    p.decls


{-| A function binding, at the top level or in a `let`: its name, parameters, body and annotation.
-}
type alias Function =
    { name : String, args : List Src.Pattern, body : Src.Expr, annotation : Maybe Src.Type }


{-| The top-level functions of a module, in source order.
-}
functions : Parsed -> List Function
functions p =
    List.filterMap
        (\d ->
            case d of
                Decl.Value _ (A.At _ (Src.Value v)) ->
                    Just
                        { name = A.toValue (c1 v.name)
                        , args = List.map c1 v.args
                        , body = c1 v.body
                        , annotation = Maybe.map (c1 >> c2) v.tipe
                        }

                _ ->
                    Nothing
        )
        p.decls


{-| The fields a record pattern binds, in source order (eco holds them reversed, E9).
-}
recordPatternFields : Src.C1 (List (Src.C2 (A.Located String))) -> List (A.Located String)
recordPatternFields ( _, fields ) =
    List.reverse (List.map c2 fields)



-- DESCRIBING A FAILURE


{-| A failure in a few words: the row and column where the parse stopped, then the first three
constructor names of the error (`Debug.toString`), as `14:8 Declarations DeclDef DeclDefBody`.

The position is that of the innermost constructor that carries one: each constructor of eco's
error types that wraps a nested error carries the position where the nested parse began, after the
nested error, and the errors of characters, strings, numbers, escapes and space carry none.

-}
describe : E.Module -> String
describe e =
    let
        text =
            Debug.toString e

        tree =
            readNode (tokens text)

        position =
            tree |> Maybe.andThen (Tuple.first >> innermost)

        names =
            tokens text
                |> List.filterMap
                    (\t ->
                        case t of
                            TWord w ->
                                if isUpperWord w then
                                    Just w

                                else
                                    Nothing

                            _ ->
                                Nothing
                    )
                |> List.take 3
    in
    String.join " "
        ((case position of
            Just ( r, c ) ->
                [ String.fromInt r ++ ":" ++ String.fromInt c ]

            Nothing ->
                []
         )
            ++ names
        )


type Token
    = TOpen
    | TClose
    | TWord String
    | TString


type Node
    = Node String (List Arg)


type Arg
    = ANode Node
    | AInt Int
    | AOther


isUpperWord : String -> Bool
isUpperWord w =
    String.left 1 w |> String.any Char.isUpper


tokens : String -> List Token
tokens text =
    tokensHelp (String.toList text) [] |> List.reverse


tokensHelp : List Char -> List Token -> List Token
tokensHelp chars acc =
    case chars of
        [] ->
            acc

        '(' :: rest ->
            tokensHelp rest (TOpen :: acc)

        ')' :: rest ->
            tokensHelp rest (TClose :: acc)

        '"' :: rest ->
            tokensHelp (skipString rest) (TString :: acc)

        '\'' :: rest ->
            tokensHelp (skipChar rest) (TString :: acc)

        c :: rest ->
            if c == ' ' || c == '\n' then
                tokensHelp rest acc

            else
                let
                    word =
                        takeWord (c :: rest)
                in
                tokensHelp (List.drop (List.length word) (c :: rest)) (TWord (String.fromList word) :: acc)


takeWord : List Char -> List Char
takeWord chars =
    case chars of
        c :: rest ->
            if c == ' ' || c == '\n' || c == '(' || c == ')' || c == '"' then
                []

            else
                c :: takeWord rest

        [] ->
            []


skipString : List Char -> List Char
skipString chars =
    case chars of
        '\\' :: _ :: rest ->
            skipString rest

        '"' :: rest ->
            rest

        _ :: rest ->
            skipString rest

        [] ->
            []


skipChar : List Char -> List Char
skipChar chars =
    case chars of
        '\\' :: _ :: rest ->
            skipChar rest

        '\'' :: rest ->
            rest

        _ :: rest ->
            skipChar rest

        [] ->
            []


{-| A constructor and its arguments, up to the closing parenthesis or the end; and the tokens left.
-}
readNode : List Token -> Maybe ( Node, List Token )
readNode ts =
    case ts of
        (TWord name) :: rest ->
            let
                ( args, left ) =
                    readArgs rest []
            in
            Just ( Node name args, left )

        _ ->
            Nothing


readArgs : List Token -> List Arg -> ( List Arg, List Token )
readArgs ts acc =
    case ts of
        TOpen :: rest ->
            case readNode rest of
                Just ( n, TClose :: left ) ->
                    readArgs left (ANode n :: acc)

                Just ( n, left ) ->
                    readArgs left (ANode n :: acc)

                Nothing ->
                    readArgs rest acc

        (TWord w) :: rest ->
            readArgs rest
                ((case String.toInt w of
                    Just n ->
                        AInt n

                    Nothing ->
                        if isUpperWord w then
                            ANode (Node w [])

                        else
                            AOther
                 )
                    :: acc
                )

        TString :: rest ->
            readArgs rest (AOther :: acc)

        TClose :: _ ->
            ( List.reverse acc, ts )

        [] ->
            ( List.reverse acc, [] )


{-| The constructors of eco's error types that carry no position (`Compiler.Parse.Error`: `Space`,
`Char`, `String_`, `Number`, `Escape`) and of `Compiler.Lexer.Symbol.BadOperator`.
-}
positionless : List String
positionless =
    [ "HasTab", "EndlessMultiComment", "CharEndless", "CharEscape", "CharNotString", "StringEndless_Single", "StringEndless_Multi", "StringEscape", "NumberEnd", "NumberDot", "NumberHexDigit", "NumberNoLeadingZero", "NumberInexactOnHost", "EscapeUnknown", "BadUnicodeFormat", "BadUnicodeCode", "BadUnicodeLength", "BadDot", "BadPipe", "BadArrow", "BadEquals", "BadHasType" ]


innermost : Node -> Maybe ( Int, Int )
innermost (Node name args) =
    let
        nested =
            args
                |> List.filterMap
                    (\a ->
                        case a of
                            ANode n ->
                                innermost n

                            _ ->
                                Nothing
                    )
                |> List.head

        own =
            if List.member name positionless then
                Nothing

            else
                case List.reverse args of
                    (AInt c) :: (AInt r) :: _ ->
                        Just ( r, c )

                    _ ->
                        Nothing
    in
    case nested of
        Just p ->
            Just p

        Nothing ->
            own


{-| The fields of a record type `{ l1 : t1, ... }`, through parentheses; `Nothing` for any other
type.
-}
recordType : Src.Type -> Maybe (List (Src.C2 ( Src.C1 (A.Located String), Src.C1 Src.Type )))
recordType (A.At _ t) =
    case t of
        Src.TRecord fields _ ->
            Just fields

        Src.TParens ( _, inner ) ->
            recordType inner

        _ ->
            Nothing



-- LITERALS


{-| The value of a string literal. eco holds a literal's text escaped (in JavaScript's escapes,
`'\u{1F600}'` as `\uD83D\uDE00`), not its value (E8).
-}
stringValue : String -> String
stringValue text =
    StringLiteral.codePoints text |> List.map Char.fromCode |> String.fromList


{-| The value of a character literal (see `stringValue`).
-}
charValue : String -> Char
charValue text =
    StringLiteral.codePoints text |> List.head |> Maybe.withDefault 0 |> Char.fromCode
