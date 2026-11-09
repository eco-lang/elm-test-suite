module Standard exposing
    ( Block(..)
    , Chapter
    , ChapterSummary
    , Comment
    , Group
    , Index
    , IndexChapter
    , IndexRule
    , IndexItem
    , Inline(..)
    , Item
    , ItemKind(..)
    , ItemLink
    , ItemPlace
    , ItemRef
    , ListItem
    , Math(..)
    , Place
    , Ref
    , RefKind(..)
    , Rule
    , RuleLink
    , Section
    , Table
    , TableCell
    , TableRow
    , chapter
    , chapterHeading
    , index
    , item
    , itemKindFromString
    , itemKindToString
    , rule
    )

{-| A Standard Definition of Elm?, as `runner/definition-data.js` writes it under `data-standard/`:
the book's text as blocks and inlines, with its mathematics already rendered by KaTeX into a tree of
elements.
-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import FatalError exposing (FatalError)
import Json.Decode as Decode exposing (Decoder)



-- TYPES


{-| KaTeX's rendering of a formula: elements and text.
-}
type Math
    = MathText String
    | MathElement String (List ( String, String )) (List Math)


type Inline
    = Text String
    | Emph (List Inline)
    | Strong (List Inline)
    | Code String
    | Sup (List Inline)
    | Break
    | InlineMath (List Math)
    | RefTo Ref
    | Anchor String
    | Raw String


type RefKind
    = ToChapter
    | ToSection
    | ToFigure
    | ToRule
    | ToItem ItemKind String


{-| The citable items other than rules, each with a page: a syntactic or further restriction, a
derived form, an entry of the initial basis (a type with its constructors, or a value), and a
figure.
-}
type ItemKind
    = Restriction
    | DerivedForm
    | BasisEntry
    | FigureItem


{-| An item stated in a list or table of the text, with the anchor it has there.
-}
type alias ItemRef =
    { kind : ItemKind
    , slug : String
    , id : String
    }


type alias ListItem =
    { item : Maybe ItemRef
    , content : List Block
    }


type alias Ref =
    { kind : RefKind
    , chapter : String
    , anchor : String
    , text : String
    , rule : Maybe String
    }


type Block
    = Paragraph (List Inline)
    | Heading { level : Int, number : Maybe String, id : String, title : List Inline }
    | DisplayMath (List Math)
    | List_ { ordered : Bool, items : List ListItem }
    | Quote (List Block)
    | Div String (List Block)
    | Figure { id : String, number : Int, caption : List Inline, content : List Block }
    | TableBlock Table
    | Pre String
    | RuleGroup { title : List Inline, judgement : List Math }
    | RuleBlock { slug : String, number : Int, id : String, math : List Math }
    | Comments (List Comment)
    | RawBlock String


type alias Comment =
    { rule : String
    , number : Maybe Int
    , content : List Block
    }


type alias Table =
    { columns : List { align : String, wrap : Bool }
    , rows : List TableRow
    , ruleBelow : Bool
    }


type alias TableRow =
    { rule : Bool
    , cells : List TableCell
    , item : Maybe ItemRef
    }


type alias TableCell =
    { content : List Inline
    , span : Int
    , align : String
    }


type alias ChapterSummary =
    { slug : String
    , number : Maybe String
    , title : List Inline
    , part : String
    }


type alias Section =
    { level : Int
    , number : Maybe String
    , id : String
    , title : List Inline
    }


type alias IndexChapter =
    { summary : ChapterSummary
    , rules : Maybe ( Int, Int )
    , sections : List Section
    }


type alias IndexRule =
    { slug : String
    , number : Int
    , chapter : String
    , group : List Inline
    }


type alias Index =
    { title : String
    , edition : String
    , author : String
    , pdf : Maybe String
    , chapters : List IndexChapter
    , rules : List IndexRule
    , items : List IndexItem
    }


{-| An item in the lists of items: `summary` is its first sentence for a restriction, and its two
forms for a derived form. `number` is a figure's number.
-}
type alias IndexItem =
    { kind : ItemKind
    , slug : String
    , chapter : String
    , section : Maybe String
    , group : Maybe (List Inline)
    , title : Maybe (List Inline)
    , summary : List (List Inline)
    , number : Maybe Int
    }


type alias Chapter =
    { summary : ChapterSummary
    , blocks : List Block
    , prev : Maybe ChapterSummary
    , next : Maybe ChapterSummary
    }


type alias Group =
    { title : List Inline
    , judgement : List Math
    }


{-| A place in the book that refers to a rule or an item.
-}
type alias Place =
    { chapter : ChapterSummary
    , section : Maybe String
    , sectionTitle : List Inline
    , anchor : String
    , comment : Maybe String
    }


type alias RuleLink =
    { slug : String
    , number : Int
    }


type alias Rule =
    { slug : String
    , number : Int
    , chapter : ChapterSummary
    , section : Maybe Section
    , group : Maybe Group
    , math : List Math
    , premises : String
    , conclusion : String
    , comments : List (List Block)
    , referencedFrom : List Place
    , prev : Maybe RuleLink
    , next : Maybe RuleLink
    }


{-| A place where an item is stated or defined: the statement of a restriction or derived form;
for an entry of the basis, its rows in the static and dynamic basis ("static", "dynamic"), the
definitions of its APPLY ("apply") and its text in Elm ("elm").
-}
type alias ItemPlace =
    { role : String
    , chapter : ChapterSummary
    , section : Maybe Section
    , figure : Maybe { number : Int, id : String, caption : List Inline }
    , blocks : List Block
    }


type alias ItemLink =
    { slug : String
    , title : Maybe (List Inline)
    }


type alias Item =
    { kind : ItemKind
    , slug : String
    , title : Maybe (List Inline)
    , group : Maybe (List Inline)
    , chapter : ChapterSummary
    , section : Maybe Section
    , anchor : String
    , places : List ItemPlace
    , referencedFrom : List Place
    , prev : Maybe ItemLink
    , next : Maybe ItemLink
    , number : Maybe Int
    }


{-| The kinds as the data names them, which are also the folders of their pages' data.
-}
itemKindToString : ItemKind -> String
itemKindToString kind =
    case kind of
        Restriction ->
            "restriction"

        DerivedForm ->
            "derived-form"

        BasisEntry ->
            "basis"

        FigureItem ->
            "figure"


itemKindFromString : String -> Maybe ItemKind
itemKindFromString s =
    case s of
        "restriction" ->
            Just Restriction

        "derived-form" ->
            Just DerivedForm

        "basis" ->
            Just BasisEntry

        "figure" ->
            Just FigureItem

        _ ->
            Nothing


{-| "Chapter 4" or "Appendix C", or the title alone for an unnumbered chapter.
-}
chapterHeading : ChapterSummary -> String
chapterHeading ch =
    case ch.number of
        Just n ->
            if ch.part == "appendix" then
                "Appendix " ++ n

            else
                "Chapter " ++ n

        Nothing ->
            ""



-- LOADING


load : Decoder a -> String -> BackendTask FatalError a
load decoder path =
    BackendTask.File.jsonFile decoder path
        |> BackendTask.allowFatal


index : BackendTask FatalError Index
index =
    load indexDecoder "data-standard/index.json"


chapter : String -> BackendTask FatalError Chapter
chapter slug =
    load chapterDecoder ("data-standard/chapters/" ++ slug ++ ".json")


rule : String -> BackendTask FatalError Rule
rule slug =
    load ruleDecoder ("data-standard/rules/" ++ slug ++ ".json")


item : ItemKind -> String -> BackendTask FatalError Item
item kind slug =
    load itemDecoder ("data-standard/items/" ++ itemKindToString kind ++ "/" ++ slug ++ ".json")



-- DECODERS


mathDecoder : Decoder Math
mathDecoder =
    Decode.oneOf
        [ Decode.map MathText Decode.string
        , Decode.map3 MathElement
            (Decode.index 0 Decode.string)
            (Decode.index 1 (Decode.keyValuePairs Decode.string))
            (Decode.index 2 (Decode.list (Decode.lazy (\_ -> mathDecoder))))
        ]


mathListDecoder : Decoder (List Math)
mathListDecoder =
    Decode.oneOf
        [ Decode.list mathDecoder
        , Decode.null []
        ]


inlinesDecoder : Decoder (List Inline)
inlinesDecoder =
    Decode.list (Decode.lazy (\_ -> inlineDecoder))


inlineDecoder : Decoder Inline
inlineDecoder =
    Decode.oneOf
        [ Decode.map Text Decode.string
        , Decode.field "t" Decode.string |> Decode.andThen inlineOf
        ]


inlineOf : String -> Decoder Inline
inlineOf t =
    case t of
        "em" ->
            Decode.map Emph (Decode.field "c" inlinesDecoder)

        "strong" ->
            Decode.map Strong (Decode.field "c" inlinesDecoder)

        "code" ->
            Decode.map Code (Decode.field "v" Decode.string)

        "sup" ->
            Decode.map Sup (Decode.field "c" inlinesDecoder)

        "br" ->
            Decode.succeed Break

        "m" ->
            Decode.map InlineMath (Decode.field "m" mathListDecoder)

        "ref" ->
            Decode.map RefTo refDecoder

        "anchor" ->
            Decode.map Anchor (Decode.field "id" Decode.string)

        "raw" ->
            Decode.map Raw (Decode.field "tex" Decode.string)

        _ ->
            Decode.fail ("unknown inline " ++ t)


refDecoder : Decoder Ref
refDecoder =
    Decode.map5 Ref
        (Decode.field "kind" Decode.string
            |> Decode.andThen
                (\k ->
                    let
                        toItem kind =
                            Decode.map (ToItem kind) (Decode.field "item" Decode.string)
                    in
                    case k of
                        "ch" ->
                            Decode.succeed ToChapter

                        "fig" ->
                            Decode.succeed ToFigure

                        "rule" ->
                            Decode.succeed ToRule

                        "res" ->
                            toItem Restriction

                        "df" ->
                            toItem DerivedForm

                        "b" ->
                            toItem BasisEntry

                        _ ->
                            Decode.succeed ToSection
                )
        )
        (Decode.oneOf [ Decode.field "chapter" Decode.string, Decode.succeed "" ])
        (Decode.oneOf [ Decode.field "anchor" Decode.string, Decode.succeed "" ])
        (Decode.field "text" Decode.string)
        (Decode.maybe (Decode.field "rule" Decode.string))


blocksDecoder : Decoder (List Block)
blocksDecoder =
    Decode.list (Decode.lazy (\_ -> blockDecoder))


blockDecoder : Decoder Block
blockDecoder =
    Decode.field "t" Decode.string |> Decode.andThen blockOf


blockOf : String -> Decoder Block
blockOf t =
    case t of
        "p" ->
            Decode.map Paragraph (Decode.field "c" inlinesDecoder)

        "h" ->
            Decode.map4 (\level number id title -> Heading { level = level, number = number, id = id, title = title })
                (Decode.field "level" Decode.int)
                (Decode.field "number" (Decode.nullable Decode.string))
                (Decode.field "id" Decode.string)
                (Decode.field "c" inlinesDecoder)

        "math" ->
            Decode.map DisplayMath (Decode.field "m" mathListDecoder)

        "list" ->
            Decode.map2 (\ordered items -> List_ { ordered = ordered, items = items })
                (Decode.field "ordered" Decode.bool)
                (Decode.field "items"
                    (Decode.list
                        (Decode.map2 ListItem
                            (Decode.maybe (Decode.field "item" itemRefDecoder))
                            (Decode.field "c" blocksDecoder)
                        )
                    )
                )

        "quote" ->
            Decode.map Quote (Decode.field "c" blocksDecoder)

        "div" ->
            Decode.map2 Div (Decode.field "cls" Decode.string) (Decode.field "c" blocksDecoder)

        "figure" ->
            Decode.map4 (\id number caption content -> Figure { id = id, number = number, caption = caption, content = content })
                (Decode.oneOf [ Decode.field "id" Decode.string, Decode.succeed "" ])
                (Decode.field "number" Decode.int)
                (Decode.field "caption" inlinesDecoder)
                (Decode.field "c" blocksDecoder)

        "table" ->
            Decode.map TableBlock tableDecoder

        "pre" ->
            Decode.map Pre (Decode.field "v" Decode.string)

        "rulegroup" ->
            Decode.map2 (\title judgement -> RuleGroup { title = title, judgement = judgement })
                (Decode.field "title" inlinesDecoder)
                (Decode.field "judgement" mathListDecoder)

        "rule" ->
            Decode.map4 (\slug number id math -> RuleBlock { slug = slug, number = number, id = id, math = math })
                (Decode.field "slug" Decode.string)
                (Decode.field "number" Decode.int)
                (Decode.field "id" Decode.string)
                (Decode.field "m" mathListDecoder)

        "comments" ->
            Decode.map Comments
                (Decode.field "items"
                    (Decode.list
                        (Decode.map3 Comment
                            (Decode.field "rule" Decode.string)
                            (Decode.field "number" (Decode.nullable Decode.int))
                            (Decode.field "c" blocksDecoder)
                        )
                    )
                )

        "raw" ->
            Decode.map RawBlock (Decode.field "tex" Decode.string)

        _ ->
            Decode.fail ("unknown block " ++ t)


tableDecoder : Decoder Table
tableDecoder =
    Decode.map3 Table
        (Decode.field "cols"
            (Decode.list
                (Decode.map2 (\align wrap -> { align = align, wrap = wrap })
                    (Decode.field "align" Decode.string)
                    (Decode.field "wrap" Decode.bool)
                )
            )
        )
        (Decode.field "rows"
            (Decode.list
                (Decode.map3 TableRow
                    (Decode.field "rule" Decode.bool)
                    (Decode.field "cells"
                        (Decode.list
                            (Decode.map3 TableCell
                                (Decode.field "c" inlinesDecoder)
                                (Decode.field "span" Decode.int)
                                (Decode.field "align" Decode.string)
                            )
                        )
                    )
                    (Decode.maybe (Decode.field "item" itemRefDecoder))
                )
            )
        )
        (Decode.field "ruleBelow" Decode.bool)


chapterSummaryDecoder : Decoder ChapterSummary
chapterSummaryDecoder =
    Decode.map4 ChapterSummary
        (Decode.field "slug" Decode.string)
        (Decode.field "number" (Decode.nullable Decode.string))
        (Decode.field "title" inlinesDecoder)
        (Decode.field "part" Decode.string)


sectionDecoder : Decoder Section
sectionDecoder =
    Decode.map4 Section
        (Decode.field "level" Decode.int)
        (Decode.field "number" (Decode.nullable Decode.string))
        (Decode.field "id" Decode.string)
        (Decode.field "title" inlinesDecoder)


indexDecoder : Decoder Index
indexDecoder =
    Decode.succeed Index
        |> andMap (Decode.field "title" Decode.string)
        |> andMap (Decode.field "edition" Decode.string)
        |> andMap (Decode.field "author" Decode.string)
        |> andMap (Decode.field "pdf" (Decode.nullable Decode.string))
        |> andMap (Decode.field "chapters"
            (Decode.list
                (Decode.map3 IndexChapter
                    chapterSummaryDecoder
                    (Decode.field "rules"
                        (Decode.nullable
                            (Decode.map2 Tuple.pair (Decode.index 0 Decode.int) (Decode.index 1 Decode.int))
                        )
                    )
                    (Decode.field "sections" (Decode.list sectionDecoder))
                )
            )
        )
        |> andMap
            (Decode.field "rules"
                (Decode.list
                    (Decode.map4 IndexRule
                        (Decode.field "slug" Decode.string)
                        (Decode.field "number" Decode.int)
                        (Decode.field "chapter" Decode.string)
                        (Decode.field "group" inlinesDecoder)
                    )
                )
            )
        |> andMap
            (Decode.field "items"
                (Decode.list
                    (Decode.map8 IndexItem
                        (Decode.field "kind" itemKindDecoder)
                        (Decode.field "slug" Decode.string)
                        (Decode.field "chapter" Decode.string)
                        (Decode.field "section" (Decode.nullable Decode.string))
                        (Decode.field "group" (Decode.nullable inlinesDecoder))
                        (Decode.field "title" (Decode.nullable inlinesDecoder))
                        (Decode.field "summary" (Decode.list inlinesDecoder))
                        numberDecoder
                    )
                )
            )


itemKindDecoder : Decoder ItemKind
itemKindDecoder =
    Decode.string
        |> Decode.andThen
            (\s ->
                case itemKindFromString s of
                    Just k ->
                        Decode.succeed k

                    Nothing ->
                        Decode.fail ("unknown kind of item " ++ s)
            )


itemRefDecoder : Decoder ItemRef
itemRefDecoder =
    Decode.map3 ItemRef
        (Decode.field "kind" itemKindDecoder)
        (Decode.field "slug" Decode.string)
        (Decode.field "id" Decode.string)


{-| A section as a rule or an item records it: without its level.
-}
placeSectionDecoder : Decoder Section
placeSectionDecoder =
    Decode.map3 (\number id title -> Section 1 number id title)
        (Decode.field "number" (Decode.nullable Decode.string))
        (Decode.field "id" Decode.string)
        (Decode.field "title" inlinesDecoder)


placeDecoder : Decoder Place
placeDecoder =
    Decode.map5 Place
        (Decode.field "chapter" chapterSummaryDecoder)
        (Decode.field "section" (Decode.nullable Decode.string))
        (Decode.field "sectionTitle" (Decode.oneOf [ inlinesDecoder, Decode.null [] ]))
        (Decode.field "anchor" Decode.string)
        (Decode.field "comment" (Decode.nullable Decode.string))


itemLinkDecoder : Decoder ItemLink
itemLinkDecoder =
    Decode.map2 ItemLink
        (Decode.field "slug" Decode.string)
        (Decode.field "title" (Decode.nullable inlinesDecoder))


itemDecoder : Decoder Item
itemDecoder =
    Decode.succeed Item
        |> andMap (Decode.field "kind" itemKindDecoder)
        |> andMap (Decode.field "slug" Decode.string)
        |> andMap (Decode.field "title" (Decode.nullable inlinesDecoder))
        |> andMap (Decode.field "group" (Decode.nullable inlinesDecoder))
        |> andMap (Decode.field "chapter" chapterSummaryDecoder)
        |> andMap (Decode.field "section" (Decode.nullable placeSectionDecoder))
        |> andMap (Decode.field "anchor" Decode.string)
        |> andMap
            (Decode.field "places"
                (Decode.list
                    (Decode.map5 ItemPlace
                        (Decode.field "role" Decode.string)
                        (Decode.field "chapter" chapterSummaryDecoder)
                        (Decode.field "section" (Decode.nullable placeSectionDecoder))
                        (Decode.field "figure"
                            (Decode.nullable
                                (Decode.map3 (\number id caption -> { number = number, id = id, caption = caption })
                                    (Decode.field "number" Decode.int)
                                    (Decode.field "id" Decode.string)
                                    (Decode.field "caption" inlinesDecoder)
                                )
                            )
                        )
                        (Decode.field "blocks" blocksDecoder)
                    )
                )
            )
        |> andMap (Decode.field "referencedFrom" (Decode.list placeDecoder))
        |> andMap (Decode.field "prev" (Decode.nullable itemLinkDecoder))
        |> andMap (Decode.field "next" (Decode.nullable itemLinkDecoder))
        |> andMap numberDecoder


{-| A figure's number; the other items have none.
-}
numberDecoder : Decoder (Maybe Int)
numberDecoder =
    Decode.oneOf [ Decode.field "number" (Decode.nullable Decode.int), Decode.succeed Nothing ]


chapterDecoder : Decoder Chapter
chapterDecoder =
    Decode.map4 Chapter
        chapterSummaryDecoder
        (Decode.field "blocks" blocksDecoder)
        (Decode.field "prev" (Decode.nullable chapterSummaryDecoder))
        (Decode.field "next" (Decode.nullable chapterSummaryDecoder))


ruleLinkDecoder : Decoder RuleLink
ruleLinkDecoder =
    Decode.map2 RuleLink
        (Decode.field "slug" Decode.string)
        (Decode.field "number" Decode.int)


ruleDecoder : Decoder Rule
ruleDecoder =
    Decode.succeed Rule
        |> andMap (Decode.field "slug" Decode.string)
        |> andMap (Decode.field "number" Decode.int)
        |> andMap (Decode.field "chapter" chapterSummaryDecoder)
        |> andMap (Decode.field "section" (Decode.nullable placeSectionDecoder))
        |> andMap
            (Decode.field "group"
                (Decode.nullable
                    (Decode.map2 Group
                        (Decode.field "title" inlinesDecoder)
                        (Decode.field "judgement" mathListDecoder)
                    )
                )
            )
        |> andMap (Decode.field "m" mathListDecoder)
        |> andMap (Decode.at [ "tex", "premises" ] Decode.string)
        |> andMap (Decode.at [ "tex", "conclusion" ] Decode.string)
        |> andMap (Decode.field "comments" (Decode.list blocksDecoder))
        |> andMap (Decode.field "referencedFrom" (Decode.list placeDecoder))
        |> andMap (Decode.field "prev" (Decode.nullable ruleLinkDecoder))
        |> andMap (Decode.field "next" (Decode.nullable ruleLinkDecoder))


andMap : Decoder a -> Decoder (a -> b) -> Decoder b
andMap =
    Decode.map2 (|>)
