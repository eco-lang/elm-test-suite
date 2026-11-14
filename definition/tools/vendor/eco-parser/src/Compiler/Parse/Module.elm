module Compiler.Parse.Module exposing
    ( Module, Header, Effects(..)
    , chompModule, chompImports
    )

{-| Turns the text of one `.elm` file into a `Module`.

`chompModule` reads the file into a `Module`: the module header if there is
one, then the imports, then `infix` declarations, then one or more top-level
declarations, each starting in column 1. A header is one of `module` or
`port module`, each with a name and an `exposing` list, and may be followed by
the module doc comment. A file with no header is accepted too.

(Vendored from eco-compiler; see `VENDORED.md`. The checks that eco runs after
parsing, the project types and the `effect module` header are cut.)


# Module Structure

@docs Module, Header, Effects


# Parsers

@docs chompModule, chompImports

-}

import Compiler.Core.Annotation as A
import Compiler.Core.Name as Name
import Compiler.IR.Source as Src
import Compiler.Lexer.Keyword as Keyword
import Compiler.Lexer.Primitives as P exposing (Col, Row)
import Compiler.Lexer.Symbol as Symbol
import Compiler.Parse.Declaration as Decl
import Compiler.Parse.Error as E
import Compiler.Parse.Space as Space
import Compiler.Parse.Variable as Var



-- ====== Module Parsing ======


{-| A parsed module before its effects are checked, with every comment
outside the declarations still in place.

`initialComments` are the comments before the header. The comment group in
`imports` is the comments after the header and its doc comment. `imports`
holds the file's own imports in source order; `infixes` are in reverse source
order and `decls` in source order.

-}
type alias Module =
    { initialComments : Src.FComments
    , header : Maybe Header
    , imports : Src.C1 (List (Src.C1 Src.Import))
    , infixes : List (Src.C1 (A.Located Src.Infix))
    , decls : List (Src.C2 Decl.Decl)
    }


{-| A parser for a whole module: an optional header, the imports as written,
any `infix` declarations, and then at least one declaration.
-}
chompModule : P.Parser E.Module Module
chompModule =
    chompHeader
        |> P.andThen
            (\( ( initialComments, headerComments ), header ) ->
                chompImports []
                    |> P.andThen
                        (\imports ->
                            chompInfixes []
                                |> P.andThen
                                    (\infixes ->
                                        P.specialize E.Declarations chompDecls
                                            |> P.map
                                                (\decls ->
                                                    Module
                                                        initialComments
                                                        header
                                                        ( headerComments, imports )
                                                        infixes
                                                        decls
                                                )
                                    )
                        )
            )



-- ====== FRESH LINES ======


{-| Produces a parser that reads whitespace and comments and then requires the
next token to start in column 1, failing with `toFreshLineError` otherwise. It
returns the comments read.
-}
freshLine : (Row -> Col -> E.Module) -> P.Parser E.Module Src.FComments
freshLine toFreshLineError =
    Space.chomp E.ModuleSpace
        |> P.andThen
            (\comments ->
                Space.checkFreshLine toFreshLineError
                    |> P.map (\_ -> comments)
            )



-- ====== CHOMP DECLARATIONS ======


{-| A parser for one or more top-level declarations, in source order. Every
declaration after the first must start in column 1; the first needs no check,
because the parser before it has already required one.
-}
chompDecls : P.Parser E.Decl (List (Src.C2 Decl.Decl))
chompDecls =
    Decl.declaration
        |> P.andThen (\( decl, _ ) -> P.loop chompDeclsHelp [ decl ])


{-| One step of `chompDecls`: reads another declaration onto the front of
`decls` when the next line starts in column 1, and otherwise finishes with
`decls` reversed.
-}
chompDeclsHelp : List (Src.C2 Decl.Decl) -> P.Parser E.Decl (P.Step (List (Src.C2 Decl.Decl)) (List (Src.C2 Decl.Decl)))
chompDeclsHelp decls =
    P.oneOfWithFallback
        [ Space.checkFreshLine E.DeclStart
            |> P.andThen
                (\_ ->
                    Decl.declaration
                        |> P.map (\( decl, _ ) -> P.Loop (decl :: decls))
                )
        ]
        (P.Done (List.reverse decls))


{-| Produces a parser that reads `infix` declarations for as long as there are
any, pushing each onto the front of `infixes`, and returns the accumulated list
without reversing it.
-}
chompInfixes : List (Src.C1 (A.Located Src.Infix)) -> P.Parser E.Module (List (Src.C1 (A.Located Src.Infix)))
chompInfixes infixes =
    P.oneOfWithFallback
        [ Decl.infix_
            |> P.andThen (\binop -> chompInfixes (binop :: infixes))
        ]
        infixes



-- ====== MODULE DOC COMMENT ======


{-| A parser for what follows a module header: the comments up to the next line
starting in column 1, and a module doc comment there if there is one.

The result's comments are all those read, before and after the doc comment.
Without a doc comment the result is `Err` of the region of the whitespace that
was read, which is where the doc comment was expected.

-}
chompModuleDocCommentSpace : P.Parser E.Module (Src.C1 (Result A.Region Src.Comment))
chompModuleDocCommentSpace =
    P.addLocation (freshLine E.FreshLine)
        |> P.andThen
            (\(A.At region beforeComments) ->
                P.oneOfWithFallback
                    [ Space.docComment E.ImportStart E.ModuleSpace
                        |> P.andThen
                            (\docComment ->
                                Space.chomp E.ModuleSpace
                                    |> P.andThen
                                        (\afterComments ->
                                            Space.checkFreshLine E.FreshLine
                                                |> P.map
                                                    (\_ ->
                                                        ( beforeComments ++ afterComments
                                                        , Ok docComment
                                                        )
                                                    )
                                        )
                            )
                    ]
                    ( beforeComments, Err region )
            )



-- ====== Header ======


{-| A module's header: its name, its kind of effects, its `exposing` list and
its module doc comment, with the comments around them.

`docs` is `Err` of the place the doc comment was expected when the header has
none.

-}
type alias Header =
    { name : Src.C2 (A.Located Name.Name)
    , effects : Effects
    , exports : Src.C2 (A.Located Src.Exposing)
    , docs : Result A.Region Src.Comment
    }


{-| Which of the three kinds of header a module has, as written, before the
rules about effects are checked.

Each region runs from the first keyword of the header to the end of its
`module` keyword.

`NoEffects` is a plain `module` header.

`Ports` is a `port module` header, and carries the comments between `port`
and `module`.

`Manager` is an `effect module` header. The vendored parser never produces
it: its `effect module` parser is cut.

-}
type Effects
    = NoEffects A.Region
    | Ports A.Region Src.FComments
    | Manager A.Region Src.FComments (Src.C1 Src.Manager)



-- ====== HEADER PARSING HELPERS ======


{-| The error constructors a header parser reports with, which differ between a
plain module header and a port module header.
-}
type alias ModuleErrContext =
    { spaceErr : Row -> Col -> E.Module
    , nameErr : Row -> Col -> E.Module
    , exposingErr : E.Exposing -> Row -> Col -> E.Module
    }


{-| Produces a parser for the part of a plain or port module header after its
`module` keyword: the name, `exposing` and the exposing list, then the comments
and optional doc comment that follow.

`makeEffects` receives `start` and the position after `module`.

-}
chompModuleHeaderCommon :
    ModuleErrContext
    -> (A.Position -> A.Position -> Effects)
    -> Src.FComments
    -> A.Position
    -> P.Parser E.Module (Src.C2 (Maybe Header))
chompModuleHeaderCommon errCtx makeEffects initialComments start =
    P.getPosition
        |> P.andThen
            (\effectEnd ->
                Space.chompAndCheckIndent E.ModuleSpace errCtx.spaceErr
                    |> P.andThen
                        (\beforeNameComments ->
                            P.addLocation (Var.moduleName errCtx.nameErr)
                                |> P.andThen
                                    (\name ->
                                        Space.chompAndCheckIndent E.ModuleSpace errCtx.spaceErr
                                            |> P.andThen
                                                (\afterNameComments ->
                                                    Keyword.exposing_ errCtx.spaceErr
                                                        |> P.andThen (\_ -> Space.chompAndCheckIndent E.ModuleSpace errCtx.spaceErr)
                                                        |> P.andThen
                                                            (\afterExportsComments ->
                                                                P.addLocation (P.specialize errCtx.exposingErr exposing_)
                                                                    |> P.andThen
                                                                        (\exports ->
                                                                            chompModuleDocCommentSpace
                                                                                |> P.map
                                                                                    (\docCommentResult ->
                                                                                        buildHeader initialComments
                                                                                            beforeNameComments
                                                                                            name
                                                                                            afterNameComments
                                                                                            afterExportsComments
                                                                                            exports
                                                                                            (makeEffects start effectEnd)
                                                                                            docCommentResult
                                                                                    )
                                                                        )
                                                            )
                                                )
                                    )
                        )
            )


{-| Assembles a parsed header and the comment groups around its parts into the
result of a header parser.
-}
buildHeader :
    Src.FComments
    -> Src.FComments
    -> A.Located Name.Name
    -> Src.FComments
    -> Src.FComments
    -> A.Located Src.Exposing
    -> Effects
    -> Src.C1 (Result A.Region Src.Comment)
    -> Src.C2 (Maybe Header)
buildHeader initialComments beforeNameComments name afterNameComments afterExportsComments exports effects ( headerComments, docComment ) =
    ( ( initialComments, headerComments )
    , Just <|
        Header
            ( ( beforeNameComments, afterNameComments ), name )
            effects
            ( ( [], afterExportsComments ), exports )
            docComment
    )


{-| A parser for the comments at the top of a file and the module header after
them, if there is one.

The first comment group of the result is the comments before the header, and
the second those after it. With no header the second group is empty and the
header is `Nothing`.

-}
chompHeader : P.Parser E.Module (Src.C2 (Maybe Header))
chompHeader =
    freshLine E.FreshLine
        |> P.andThen
            (\initialComments ->
                P.getPosition
                    |> P.andThen
                        (\start ->
                            P.oneOfWithFallback
                                [ chompNormalModule initialComments start
                                , chompPortModule initialComments start
                                ]
                                ( ( initialComments, [] ), Nothing )
                        )
            )


{-| Produces a parser for a `module` header starting at `start`.
-}
chompNormalModule : Src.FComments -> A.Position -> P.Parser E.Module (Src.C2 (Maybe Header))
chompNormalModule initialComments start =
    let
        errCtx : ModuleErrContext
        errCtx =
            { spaceErr = E.ModuleProblem
            , nameErr = E.ModuleName
            , exposingErr = E.ModuleExposing
            }
    in
    Keyword.module_ E.ModuleProblem
        |> P.andThen (\_ -> chompModuleHeaderCommon errCtx (\s e -> NoEffects (A.Region s e)) initialComments start)


{-| Produces a parser for a `port module` header starting at `start`.
-}
chompPortModule : Src.FComments -> A.Position -> P.Parser E.Module (Src.C2 (Maybe Header))
chompPortModule initialComments start =
    let
        errCtx : ModuleErrContext
        errCtx =
            { spaceErr = E.PortModuleProblem
            , nameErr = E.PortModuleName
            , exposingErr = E.PortModuleExposing
            }
    in
    Keyword.port_ E.PortModuleProblem
        |> P.andThen (\_ -> Space.chompAndCheckIndent E.ModuleSpace E.PortModuleProblem)
        |> P.andThen
            (\postPortComments ->
                Keyword.module_ E.PortModuleProblem
                    |> P.andThen (\_ -> chompModuleHeaderCommon errCtx (\s e -> Ports (A.Region s e) postPortComments) initialComments start)
            )


-- ====== Imports ======


{-| Produces a parser that reads import declarations for as long as there are
any, and returns `is` reversed followed by the imports read, in source order.
-}
chompImports : List (Src.C1 Src.Import) -> P.Parser E.Module (List (Src.C1 Src.Import))
chompImports is =
    P.oneOfWithFallback
        [ chompImport
            |> P.andThen (\i -> chompImports (i :: is))
        ]
        (List.reverse is)


{-| A parser for one import declaration: `import`, the module name, an
optional `as` alias and an optional `exposing` list, ending with the next token
in column 1.

The comment group is the comments after the import. An import without an
`exposing` list gets an empty explicit list placed at `A.zero`.

-}
chompImport : P.Parser E.Module (Src.C1 Src.Import)
chompImport =
    Keyword.import_ E.ImportStart
        |> P.andThen (\_ -> Space.chompAndCheckIndent E.ModuleSpace E.ImportIndentName)
        |> P.andThen
            (\preNameComments ->
                P.addLocation (Var.moduleName E.ImportName)
                    |> P.andThen
                        (\((A.At (A.Region _ end) _) as name) ->
                            Space.chomp E.ModuleSpace
                                |> P.andThen
                                    (\trailingComments ->
                                        P.oneOf E.ImportEnd
                                            [ Space.checkFreshLine E.ImportEnd
                                                |> P.map (\_ -> ( trailingComments, Src.Import ( preNameComments, name ) Nothing ( ( [], [] ), Src.Explicit (A.At A.zero []) ) ))
                                            , Space.checkIndent end E.ImportEnd
                                                |> P.andThen
                                                    (\_ ->
                                                        P.oneOf E.ImportAs
                                                            [ chompAs ( preNameComments, name ) trailingComments
                                                            , chompExposing ( preNameComments, name ) Nothing [] trailingComments
                                                            ]
                                                    )
                                            ]
                                    )
                        )
            )


{-| Produces a parser for the `as Alias` part of an import of `name` and
whatever follows it.
-}
chompAs : Src.C1 (A.Located Name.Name) -> Src.FComments -> P.Parser E.Module (Src.C1 Src.Import)
chompAs name trailingComments =
    Keyword.as_ E.ImportAs
        |> P.andThen (\_ -> Space.chompAndCheckIndent E.ModuleSpace E.ImportIndentAlias)
        |> P.andThen
            (\postAliasComments ->
                Var.upper E.ImportAlias
                    |> P.andThen
                        (\alias_ ->
                            P.getPosition
                                |> P.andThen
                                    (\end ->
                                        Space.chomp E.ModuleSpace
                                            |> P.andThen
                                                (\preExposedComments ->
                                                    let
                                                        aliasWithComments : Maybe (Src.C2 Name.Name)
                                                        aliasWithComments =
                                                            Just ( ( trailingComments, postAliasComments ), alias_ )

                                                        emptyExposing : Src.C2 Src.Exposing
                                                        emptyExposing =
                                                            ( ( [], [] ), Src.Explicit (A.At A.zero []) )
                                                    in
                                                    P.oneOf E.ImportEnd
                                                        [ Space.checkFreshLine E.ImportEnd
                                                            |> P.map (\_ -> ( preExposedComments, Src.Import name aliasWithComments emptyExposing ))
                                                        , Space.checkIndent end E.ImportEnd
                                                            |> P.andThen (\_ -> chompExposing name (Just ( postAliasComments, alias_ )) trailingComments preExposedComments)
                                                        ]
                                                )
                                    )
                        )
            )


{-| Produces a parser for the `exposing` list of an import of `name` and the
comments after it, up to the next token in column 1.
-}
chompExposing :
    Src.C1 (A.Located Name.Name)
    -> Maybe (Src.C1 Name.Name)
    -> Src.FComments
    -> Src.FComments
    -> P.Parser E.Module (Src.C1 Src.Import)
chompExposing name maybeAlias trailingComments preExposedComments =
    Keyword.exposing_ E.ImportExposing
        |> P.andThen (\_ -> Space.chompAndCheckIndent E.ModuleSpace E.ImportIndentExposingList)
        |> P.andThen
            (\postExposedComments ->
                P.specialize E.ImportExposingList exposing_
                    |> P.andThen
                        (\exposed ->
                            freshLine E.ImportEnd
                                |> P.map
                                    (\comments ->
                                        let
                                            aliasWithComments : Maybe (Src.C2 Name.Name)
                                            aliasWithComments =
                                                Maybe.map
                                                    (\( postAliasComments, alias_ ) ->
                                                        ( ( trailingComments, postAliasComments ), alias_ )
                                                    )
                                                    maybeAlias

                                            exposedWithComments : Src.C2 Src.Exposing
                                            exposedWithComments =
                                                ( ( preExposedComments, postExposedComments ), exposed )
                                        in
                                        ( comments, Src.Import name aliasWithComments exposedWithComments )
                                    )
                        )
            )



-- ====== LISTING ======


{-| A parser for an exposing list in parentheses: `(..)`, or a comma-separated
list of names.

The region of an explicit list starts just after the `(` and ends just after
the `)`.

-}
exposing_ : P.Parser E.Exposing Src.Exposing
exposing_ =
    P.word1 '(' E.ExposingStart
        |> P.andThen (\_ -> P.getPosition)
        |> P.andThen
            (\start ->
                Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentValue
                    |> P.andThen
                        (\preExposedComments ->
                            P.oneOf E.ExposingValue
                                [ P.word2 '.' '.' E.ExposingValue
                                    |> P.andThen (\_ -> Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentEnd)
                                    |> P.andThen
                                        (\postComments ->
                                            P.word1 ')' E.ExposingEnd
                                                |> P.map (\_ -> Src.Open preExposedComments postComments)
                                        )
                                , chompExposed
                                    |> P.andThen
                                        (\exposed ->
                                            Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentEnd
                                                |> P.andThen
                                                    (\postExposedComments ->
                                                        P.loop (exposingHelp start) [ ( ( preExposedComments, postExposedComments ), exposed ) ]
                                                    )
                                        )
                                ]
                        )
            )


{-| One step of `exposing_`: reads a comma and another entry onto the front of
`revExposed`, or a `)` that ends the list, which is then put back in source
order and placed from `start`.
-}
exposingHelp : A.Position -> List (Src.C2 Src.Exposed) -> P.Parser E.Exposing (P.Step (List (Src.C2 Src.Exposed)) Src.Exposing)
exposingHelp start revExposed =
    P.oneOf E.ExposingEnd
        [ P.word1 ',' E.ExposingEnd
            |> P.andThen (\_ -> Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentValue)
            |> P.andThen
                (\preExposedComments ->
                    chompExposed
                        |> P.andThen
                            (\exposed ->
                                Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentEnd
                                    |> P.map
                                        (\postExposedComments ->
                                            P.Loop (( ( preExposedComments, postExposedComments ), exposed ) :: revExposed)
                                        )
                            )
                )
        , P.word1 ')' E.ExposingEnd
            |> P.andThen (\_ -> P.getPosition)
            |> P.map (\end -> P.Done (Src.Explicit (A.At (A.Region start end) (List.reverse revExposed))))
        ]


{-| A parser for one entry of an exposing list: a value, an operator in
parentheses, or a type with its privacy.
-}
chompExposed : P.Parser E.Exposing Src.Exposed
chompExposed =
    P.getPosition
        |> P.andThen
            (\start ->
                P.oneOf E.ExposingValue
                    [ Var.lower E.ExposingValue
                        |> P.andThen
                            (\name ->
                                P.getPosition
                                    |> P.map (\end -> A.at start end name |> Src.Lower)
                            )
                    , P.word1 '(' E.ExposingValue
                        |> P.andThen (\_ -> Symbol.operator E.ExposingOperator E.ExposingOperatorReserved)
                        |> P.andThen
                            (\op ->
                                P.word1 ')' E.ExposingOperatorRightParen
                                    |> P.andThen (\_ -> P.getPosition)
                                    |> P.map (\end -> Src.Operator (A.Region start end) op)
                            )
                    , Var.upper E.ExposingValue
                        |> P.andThen
                            (\name ->
                                P.getPosition
                                    |> P.andThen
                                        (\end ->
                                            Space.chompAndCheckIndent E.ExposingSpace E.ExposingIndentEnd
                                                |> P.andThen
                                                    (\privacyComments ->
                                                        privacy
                                                            |> P.map (Src.Upper (A.at start end name) << Tuple.pair privacyComments)
                                                    )
                                        )
                            )
                    ]
            )


{-| A parser for what follows a type in an exposing list: `(..)` makes its
constructors public, with the region of the `..`. When the next character is
not `(`, the type is private and nothing is read; a `(` not followed by `..)`
is an error.
-}
privacy : P.Parser E.Exposing Src.Privacy
privacy =
    P.oneOfWithFallback
        [ P.word1 '(' E.ExposingTypePrivacy
            |> P.andThen (\_ -> Space.chompAndCheckIndent E.ExposingSpace E.ExposingTypePrivacy)
            |> P.andThen (\_ -> P.getPosition)
            |> P.andThen
                (\start ->
                    P.word2 '.' '.' E.ExposingTypePrivacy
                        |> P.andThen (\_ -> P.getPosition)
                        |> P.andThen
                            (\end ->
                                Space.chompAndCheckIndent E.ExposingSpace E.ExposingTypePrivacy
                                    |> P.andThen (\_ -> P.word1 ')' E.ExposingTypePrivacy)
                                    |> P.map (\_ -> Src.Public (A.Region start end))
                            )
                )
        ]
        Src.Private
