module Standard.ItemView exposing (crumbs, description, itemFoot, itemKey, itemNoun, itemPage, listPage, listTitle)

{-| The pages of the citable items other than rules (restrictions, derived forms, entries of the
initial basis and figures): one list page per kind, and a page for each item. Like the rest of the book, these
are put inside `View.freeze`.
-}

import Content
import Html exposing (Html)
import Html.Attributes as Attr
import Route
import Standard exposing (Index, IndexItem, Item, ItemKind(..), ItemLink, ItemPlace)
import Standard.Render as Render


listTitle : ItemKind -> String
listTitle kind =
    case kind of
        Restriction ->
            "Restrictions"

        DerivedForm ->
            "Derived forms"

        BasisEntry ->
            "The initial basis"

        FigureItem ->
            "Figures"


listHref : ItemKind -> String
listHref kind =
    Route.toString
        (case kind of
            Restriction ->
                Route.Standard__Restrictions

            DerivedForm ->
                Route.Standard__DerivedForms

            BasisEntry ->
                Route.Standard__Basis

            FigureItem ->
                Route.Standard__Figures
        )


{-| The page description of an item, for search engines and link previews.
-}
description : Index -> Item -> String
description idx it =
    Render.itemKindName it.kind ++ " " ++ it.slug ++ " of " ++ idx.title ++ " (" ++ idx.edition ++ ")"


crumbs : Index -> List (Html msg) -> Html msg
crumbs idx trail =
    Html.div [ Attr.class "ts-crumbs" ]
        (Html.a [ Attr.href (Route.toString Route.Standard) ] [ Html.text idx.title ]
            :: Html.span [ Attr.class "sd-edition-chip" ] [ Html.text idx.edition ]
            :: trail
        )


{-| The module of an entry of the basis, from its qualified name; the list type has none.
-}
moduleOf : String -> String
moduleOf slug =
    String.split "." slug |> List.reverse |> List.drop 1 |> List.reverse |> String.join "."


isType : String -> Bool
isType slug =
    String.split "." slug
        |> List.reverse
        |> List.head
        |> Maybe.andThen (String.uncons >> Maybe.map (Tuple.first >> Char.isUpper))
        |> Maybe.withDefault False



-- THE LISTS


{-| The page listing the items of a kind, with its introduction (Markdown, from content/standard/).
-}
listPage : Index -> ItemKind -> String -> Html msg
listPage idx kind intro =
    let
        items =
            List.filter (\it -> it.kind == kind) idx.items
    in
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx [ Html.text (" / " ++ listTitle kind) ]
        , Html.h1 [ Attr.class "sd-chapter-title" ] [ Html.text (listTitle kind) ]
        , Html.div [] (Content.view Content.Book Content.none intro)
        , case kind of
            Restriction ->
                Html.div [] (List.filterMap (restrictionsOf idx items) idx.chapters)

            DerivedForm ->
                derivedForms items

            BasisEntry ->
                basis items

            FigureItem ->
                Html.div [] (List.filterMap (figuresOf items) idx.chapters)
        , Render.licence idx
        ]


restrictionsOf : Index -> List IndexItem -> Standard.IndexChapter -> Maybe (Html msg)
restrictionsOf idx items ch =
    case List.filter (\it -> it.chapter == ch.summary.slug) items of
        [] ->
            Nothing

        here ->
            Just
                (Html.section [ Attr.class "ts-section", Attr.id ch.summary.slug ]
                    [ Html.h2 [ Attr.class "sd-h sd-h1" ]
                        [ Html.a [ Attr.href (Render.chapterHref ch.summary.slug "") ] (Render.chapterTitle ch.summary) ]
                    , Html.div [ Attr.class "ts-scroll" ]
                        [ Html.table [ Attr.class "ts-table sd-rules-table" ]
                            [ Html.thead []
                                [ Html.tr []
                                    [ Html.th [] [ Html.text "Restriction" ]
                                    , Html.th [] [ Html.text "Statement" ]
                                    ]
                                ]
                            , Html.tbody [] (List.map restrictionRow here)
                            ]
                        ]
                    ]
                )


restrictionRow : IndexItem -> Html msg
restrictionRow it =
    Html.tr []
        [ Html.td [ Attr.class "sd-nowrap" ]
            [ Html.a [ Attr.href (Render.itemHref it.kind it.slug), Attr.class "ts-test-name" ] [ Html.text it.slug ]
            , case it.group of
                Just g ->
                    Html.div [ Attr.class "ts-muted ts-small" ] (Render.inlines g)

                Nothing ->
                    Html.text ""
            ]
        , Html.td [] (List.concatMap Render.inlines (List.take 1 it.summary))
        ]


figuresOf : List IndexItem -> Standard.IndexChapter -> Maybe (Html msg)
figuresOf items ch =
    case List.filter (\it -> it.chapter == ch.summary.slug) items of
        [] ->
            Nothing

        here ->
            Just
                (Html.section [ Attr.class "ts-section", Attr.id ch.summary.slug ]
                    [ Html.h2 [ Attr.class "sd-h sd-h1" ]
                        [ Html.a [ Attr.href (Render.chapterHref ch.summary.slug "") ] (Render.chapterTitle ch.summary) ]
                    , Html.div [ Attr.class "ts-scroll" ]
                        [ Html.table [ Attr.class "ts-table sd-rules-table" ]
                            [ Html.thead []
                                [ Html.tr []
                                    [ Html.th [] [ Html.text "Figure" ]
                                    , Html.th [] [ Html.text "Caption" ]
                                    ]
                                ]
                            , Html.tbody []
                                (List.map
                                    (\it ->
                                        Html.tr []
                                            [ Html.td [ Attr.class "sd-nowrap" ]
                                                [ Html.a [ Attr.href (Render.itemHref it.kind it.slug), Attr.class "ts-test-name" ] [ Html.text it.slug ]
                                                , Html.div [ Attr.class "ts-muted ts-small" ] [ Html.text (figureNumber it.number) ]
                                                ]
                                            , Html.td [] (List.concatMap Render.inlines (List.take 1 it.summary))
                                            ]
                                    )
                                    here
                                )
                            ]
                        ]
                    ]
                )


figureNumber : Maybe Int -> String
figureNumber number =
    "Figure " ++ (Maybe.map String.fromInt number |> Maybe.withDefault "")


derivedForms : List IndexItem -> Html msg
derivedForms items =
    Html.div [ Attr.class "ts-scroll" ]
        [ Html.table [ Attr.class "ts-table sd-rules-table" ]
            [ Html.thead []
                [ Html.tr []
                    [ Html.th [] [ Html.text "Derived form" ]
                    , Html.th [] [ Html.text "Phrase" ]
                    , Html.th [] [ Html.text "Equivalent form" ]
                    ]
                ]
            , Html.tbody []
                (List.map
                    (\it ->
                        Html.tr []
                            [ Html.td [ Attr.class "sd-nowrap" ]
                                [ Html.a [ Attr.href (Render.itemHref it.kind it.slug), Attr.class "ts-test-name" ] [ Html.text it.slug ]
                                , case it.group of
                                    Just g ->
                                        Html.div [ Attr.class "ts-muted ts-small" ] (Render.inlines g)

                                    Nothing ->
                                        Html.text ""
                                ]
                            , Html.td [] (List.concatMap Render.inlines (List.take 1 it.summary))
                            , Html.td [] (List.concatMap Render.inlines (List.drop 1 it.summary))
                            ]
                    )
                    items
                )
            ]
        ]


basis : List IndexItem -> Html msg
basis items =
    let
        modules =
            List.foldl
                (\it acc ->
                    let
                        m =
                            moduleOf it.slug
                    in
                    if List.member m acc then
                        acc

                    else
                        acc ++ [ m ]
                )
                []
                items

        names its =
            Html.span [ Attr.class "sd-basis-names" ]
                (List.map
                    (\it ->
                        Html.a [ Attr.href (Render.itemHref it.kind it.slug), Attr.class "sd-basis-name" ]
                            [ Html.text (String.split "." it.slug |> List.reverse |> List.head |> Maybe.withDefault it.slug) ]
                    )
                    its
                )

        row label its =
            if List.isEmpty its then
                Html.text ""

            else
                Html.div [ Attr.class "sd-basis-row" ] [ Html.span [ Attr.class "sd-basis-label" ] [ Html.text label ], names its ]
    in
    Html.div []
        (List.map
            (\m ->
                let
                    its =
                        List.filter (\it -> moduleOf it.slug == m) items
                in
                Html.section [ Attr.class "ts-section", Attr.id (moduleId m) ]
                    [ Html.h2 [ Attr.class "sd-h sd-h1" ]
                        [ if String.isEmpty m then
                            Html.text "In scope in every module"

                          else
                            Html.code [] [ Html.text m ]
                        ]
                    , row "Types" (List.filter (.slug >> isType) its)
                    , row "Values" (List.filter (.slug >> isType >> not) its)
                    ]
            )
            modules
        )


moduleId : String -> String
moduleId m =
    if String.isEmpty m then
        "everywhere"

    else
        String.replace "." "-" m



-- AN ITEM


itemPage : Index -> Item -> Html msg
itemPage idx it =
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx
            [ Html.text " / "
            , Html.a [ Attr.href (listHref it.kind) ] [ Html.text (listTitle it.kind) ]
            ]
        , Html.h1 [ Attr.class "sd-chapter-title" ]
            [ Html.text (Render.itemKindName it.kind)
            , Html.code [ Attr.class "sd-rule-slug" ] [ Html.text it.slug ]
            ]
        , Html.p [ Attr.class "sd-item-meta" ] (meta it)
        , case it.kind of
            BasisEntry ->
                Html.div [] (List.filterMap (basisPart it) [ "static", "dynamic", "apply", "elm" ])

            _ ->
                Html.div [ Attr.class "sd-text" ] (List.concatMap (.blocks >> Render.blocks) it.places)
        , Html.div [ Attr.class "sd-rule-actions" ]
            [ Html.a [ Attr.href (Render.chapterHref it.chapter.slug it.anchor) ] [ Html.text "Read it in its chapter" ]
            , Html.span [ Attr.class "ts-muted" ] [ Html.text "·" ]
            , Html.span [ Attr.class "ts-muted" ]
                [ Html.text "Permanent address: "
                , Html.code [] [ Html.text (Render.itemHref it.kind it.slug) ]
                ]
            ]
        , if List.isEmpty it.referencedFrom then
            Html.text ""

          else
            Html.section [ Attr.class "ts-section" ]
                [ Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text "Referred to from" ]
                , Html.ul [ Attr.class "sd-list" ] (List.map Render.place it.referencedFrom)
                ]
        ]


{-| The foot of an item's page, after its Discussions section.
-}
itemFoot : Index -> Item -> Html msg
itemFoot idx it =
    Html.div [ Attr.class "sd-book" ]
        [ Html.nav [ Attr.class "sd-pager" ]
            [ pagerLink it.kind "Previous" it.prev
            , pagerLink it.kind "Next" it.next
            ]
        , Render.licence idx
        ]


{-| The key of an item in the titles of discussions about it: its label, `res:core-no-float-pattern`.
-}
itemKey : ItemKind -> String -> String
itemKey kind slug =
    (case kind of
        Restriction ->
            "res:"

        DerivedForm ->
            "df:"

        BasisEntry ->
            "b:"

        FigureItem ->
            "fig:"
    )
        ++ slug


itemNoun : ItemKind -> String
itemNoun kind =
    case kind of
        Restriction ->
            "restriction"

        DerivedForm ->
            "derived form"

        BasisEntry ->
            "basis entry"

        FigureItem ->
            "figure"


meta : Item -> List (Html msg)
meta it =
    let
        stated =
            case it.kind of
                BasisEntry ->
                    if String.isEmpty (moduleOf it.slug) then
                        [ Html.text "The list type and its constructors, in scope in every module. Its type is in " ]

                    else if isType it.slug then
                        [ Html.text "A type of ", Html.code [] [ Html.text (moduleOf it.slug) ], Html.text ", with its constructors. Its type is in " ]

                    else
                        [ Html.text "A value of ", Html.code [] [ Html.text (moduleOf it.slug) ], Html.text ". Its type is in " ]

                FigureItem ->
                    [ Html.strong [] [ Html.text (figureNumber it.number) ], Html.text ", " ]
                        ++ (case it.title of
                                Just t ->
                                    Render.inlines t ++ [ Html.text ", in " ]

                                Nothing ->
                                    [ Html.text "in " ]
                           )

                _ ->
                    [ Html.text "Stated in " ]

        where_ =
            Html.a [ Attr.href (Render.chapterHref it.chapter.slug (it.section |> Maybe.map .id |> Maybe.withDefault "")) ]
                (case it.section of
                    Just s ->
                        Html.text ("Section " ++ Maybe.withDefault "" s.number ++ " ") :: Render.inlines s.title

                    Nothing ->
                        Render.chapterTitle it.chapter
                )

        named =
            case
                ( if it.kind == FigureItem then
                    Nothing

                  else
                    it.title
                , it.group
                )
            of
                ( Just t, _ ) ->
                    [ Html.text ", under " ] ++ [ Html.strong [] (Render.inlines t) ]

                ( Nothing, Just g ) ->
                    [ Html.text ", under " ] ++ [ Html.strong [] (Render.inlines g) ]

                _ ->
                    []
    in
    stated ++ [ where_ ] ++ named ++ [ Html.text "." ]


basisPart : Item -> String -> Maybe (Html msg)
basisPart it role =
    case List.filter (\p -> p.role == role) it.places of
        [] ->
            Nothing

        places ->
            Just
                (Html.section [ Attr.class "ts-section" ]
                    (Html.h2 [ Attr.class "sd-h sd-h1" ] (roleTitle role)
                        :: List.map placeView places
                    )
                )


roleTitle : String -> List (Html msg)
roleTitle role =
    case role of
        "static" ->
            [ Html.text "Static basis" ]

        "dynamic" ->
            [ Html.text "Dynamic basis" ]

        "apply" ->
            [ Html.text "Its ", Html.em [] [ Html.text "APPLY" ] ]

        _ ->
            [ Html.text "Its text in Elm" ]


placeView : ItemPlace -> Html msg
placeView p =
    Html.div [ Attr.class "sd-item-place" ]
        [ Html.div [ Attr.class "sd-text" ] (Render.blocks p.blocks)
        , Html.div [ Attr.class "sd-item-source ts-muted ts-small" ]
            (case p.figure of
                Just f ->
                    [ Html.a [ Attr.href (Render.chapterHref p.chapter.slug f.id) ] [ Html.text ("Figure " ++ String.fromInt f.number) ]
                    , Html.text ": "
                    ]
                        ++ Render.inlines f.caption

                Nothing ->
                    case p.section of
                        Just s ->
                            [ Html.a [ Attr.href (Render.chapterHref p.chapter.slug s.id) ]
                                (Html.text ("Section " ++ Maybe.withDefault "" s.number ++ " ") :: Render.inlines s.title)
                            ]

                        Nothing ->
                            [ Html.a [ Attr.href (Render.chapterHref p.chapter.slug "") ] (Render.chapterTitle p.chapter) ]
            )
        ]


pagerLink : ItemKind -> String -> Maybe ItemLink -> Html msg
pagerLink kind label maybe =
    case maybe of
        Just l ->
            Html.a [ Attr.class "sd-pager-link", Attr.href (Render.itemHref kind l.slug) ]
                [ Html.span [ Attr.class "sd-pager-label" ] [ Html.text label ]
                , Html.code [] [ Html.text l.slug ]
                ]

        Nothing ->
            Html.span [] []
