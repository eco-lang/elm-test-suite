module Standard.Render exposing
    ( blocks
    , chapterHref
    , chapterTitle
    , inlines
    , itemHref
    , itemKindName
    , itemLink
    , licence
    , math
    , place
    , ruleHref
    )

{-| Html for the book's blocks, inlines and mathematics. Everything here is static: the pages put it
inside `View.freeze`, so it is rendered at build time and none of this code runs in the browser.
-}

import Html exposing (Html)
import Html.Attributes as Attr
import Route
import Standard exposing (Block(..), ChapterSummary, Inline(..), ItemKind(..), ItemRef, Math(..), Place, Ref, RefKind(..))
import VirtualDom



-- LINKS


chapterHref : String -> String -> String
chapterHref slug anchor =
    Route.toString (Route.Standard__Chapter_ { chapter = slug })
        ++ (if String.isEmpty anchor then
                ""

            else
                "#" ++ anchor
           )


ruleHref : String -> String
ruleHref slug =
    Route.toString (Route.Standard__Rules__Rule_ { rule = slug })


{-| The page of a restriction, derived form or entry of the basis. An entry's address is its
qualified name with the dots as slashes: `/standard/basis/Platform/Cmd/none`.
-}
itemHref : ItemKind -> String -> String
itemHref kind slug =
    case kind of
        Restriction ->
            Route.toString (Route.Standard__Restrictions__Restriction_ { restriction = slug })

        DerivedForm ->
            Route.toString (Route.Standard__DerivedForms__Form_ { form = slug })

        BasisEntry ->
            case String.split "." slug of
                first :: rest ->
                    Route.toString (Route.Standard__Basis__SPLAT_ { splat = ( first, rest ) })

                [] ->
                    Route.toString Route.Standard__Basis


itemKindName : ItemKind -> String
itemKindName kind =
    case kind of
        Restriction ->
            "Restriction"

        DerivedForm ->
            "Derived form"

        BasisEntry ->
            "Basis entry"


{-| The small link, after an item in the text, to the item's page, showing its name.
-}
itemLink : ItemRef -> Html msg
itemLink ref =
    Html.a
        [ Attr.class "sd-item-chip"
        , Attr.href (itemHref ref.kind ref.slug)
        , Attr.title (itemKindName ref.kind ++ " " ++ ref.slug ++ ": its page")
        ]
        [ Html.text ref.slug ]


{-| A place in the book that refers to a rule or an item.
-}
place : Place -> Html msg
place p =
    Html.li []
        (case p.comment of
            Just slug ->
                [ Html.text "The comment on rule "
                , Html.a [ Attr.href (ruleHref slug) ] [ Html.code [] [ Html.text slug ] ]
                , Html.text (" (" ++ Standard.chapterHeading p.chapter ++ ")")
                ]

            Nothing ->
                [ Html.a [ Attr.href (chapterHref p.chapter.slug p.anchor) ]
                    (case p.section of
                        Just n ->
                            Html.text ("Section " ++ n ++ " ") :: inlines p.sectionTitle

                        Nothing ->
                            chapterTitle p.chapter
                    )
                ]
        )


{-| The licence of the book's text, shown at the foot of every page of the book.
-}
licence : Standard.Index -> Html msg
licence idx =
    Html.p [ Attr.class "sd-licence" ]
        [ Html.em [] [ Html.text idx.title ]
        , Html.text (" (" ++ idx.edition ++ ") © " ++ idx.author ++ ". The text is licensed under ")
        , Html.a [ Attr.href "https://creativecommons.org/licenses/by/4.0/", Attr.rel "license" ]
            [ Html.text "CC BY 4.0" ]
        , Html.text ": share and adapt it freely, with credit and a link to the licence."
        ]


{-| "4 Static Semantics for the Core", or the title alone for an unnumbered chapter.
-}
chapterTitle : ChapterSummary -> List (Html msg)
chapterTitle ch =
    case ch.number of
        Just n ->
            Html.span [ Attr.class "sd-num" ] [ Html.text n ] :: inlines ch.title

        Nothing ->
            inlines ch.title



-- MATHEMATICS


{-| KaTeX's markup, element for element. Elements under `svg` and `math` are created in their own
namespaces, as the browser's HTML parser would create them.
-}
math : List Math -> List (Html msg)
math =
    List.map (mathNode Nothing)


mathNode : Maybe String -> Math -> Html msg
mathNode namespace node =
    case node of
        MathText t ->
            Html.text t

        MathElement tag attrs children ->
            let
                ns =
                    case tag of
                        "svg" ->
                            Just "http://www.w3.org/2000/svg"

                        "math" ->
                            Just "http://www.w3.org/1998/Math/MathML"

                        _ ->
                            namespace

                attributes =
                    List.map (\( k, v ) -> VirtualDom.attribute k v) attrs

                kids =
                    List.map (mathNode ns) children
            in
            case ns of
                Just uri ->
                    VirtualDom.nodeNS uri tag attributes kids

                Nothing ->
                    VirtualDom.node tag attributes kids



-- INLINES


inlines : List Inline -> List (Html msg)
inlines =
    List.map inline


inline : Inline -> Html msg
inline x =
    case x of
        Text t ->
            Html.text t

        Emph c ->
            Html.em [] (inlines c)

        Strong c ->
            Html.strong [] (inlines c)

        Code v ->
            Html.code [ Attr.class "sd-kw" ] [ Html.text v ]

        Sup c ->
            Html.sup [] (inlines c)

        Break ->
            Html.br [] []

        InlineMath m ->
            Html.span [ Attr.class "sd-m" ] (math m)

        RefTo ref ->
            refLink ref

        Anchor id ->
            Html.span [ Attr.id id ] []

        Raw tex ->
            Html.code [ Attr.class "sd-raw", Attr.title "Not rendered: raw TeX" ] [ Html.text tex ]


refLink : Ref -> Html msg
refLink ref =
    if String.isEmpty ref.chapter then
        Html.span [ Attr.class "sd-ref-missing" ] [ Html.text ref.text ]

    else
        let
            href =
                case ( ref.kind, ref.rule ) of
                    ( ToRule, Just slug ) ->
                        ruleHref slug

                    ( ToItem kind slug, _ ) ->
                        itemHref kind slug

                    _ ->
                        chapterHref ref.chapter ref.anchor
        in
        Html.a [ Attr.href href, Attr.class "sd-ref" ] [ Html.text ref.text ]



-- BLOCKS


blocks : List Block -> List (Html msg)
blocks =
    List.map block


block : Block -> Html msg
block b =
    case b of
        Paragraph c ->
            Html.p [ Attr.class "sd-p" ] (inlines c)

        Heading h ->
            let
                tag =
                    case h.level of
                        1 ->
                            Html.h2

                        2 ->
                            Html.h3

                        _ ->
                            Html.h4
            in
            tag [ Attr.id h.id, Attr.class ("sd-h sd-h" ++ String.fromInt h.level) ]
                (List.concat
                    [ case h.number of
                        Just n ->
                            [ Html.span [ Attr.class "sd-num" ] [ Html.text n ] ]

                        Nothing ->
                            []
                    , inlines h.title
                    , [ Html.a [ Attr.class "sd-pilcrow", Attr.href ("#" ++ h.id), Attr.title "Link to this section" ] [ Html.text "¶" ] ]
                    ]
                )

        DisplayMath m ->
            Html.div [ Attr.class "sd-display" ] (math m)

        List_ l ->
            (if l.ordered then
                Html.ol

             else
                Html.ul
            )
                [ Attr.class "sd-list" ]
                (List.map
                    (\item ->
                        case item.item of
                            Just ref ->
                                Html.li [ Attr.id ref.id, Attr.class "sd-item" ] (blocks item.content ++ [ itemLink ref ])

                            Nothing ->
                                Html.li [] (blocks item.content)
                    )
                    l.items
                )

        Quote c ->
            Html.blockquote [ Attr.class "sd-quote" ] (blocks c)

        Div cls c ->
            Html.div [ Attr.class ("sd-" ++ cls) ] (blocks c)

        Figure f ->
            Html.figure [ Attr.class "sd-figure", Attr.id f.id ]
                [ Html.div [ Attr.class "sd-figure-body" ] (blocks f.content)
                , Html.figcaption []
                    (Html.a [ Attr.href ("#" ++ f.id), Attr.class "sd-figure-num" ] [ Html.text ("Figure " ++ String.fromInt f.number) ]
                        :: Html.text ": "
                        :: inlines f.caption
                    )
                ]

        TableBlock t ->
            let
                -- Rows that are items get a last cell with the link to the item's page.
                itemCell row =
                    if List.any (\r -> r.item /= Nothing) t.rows then
                        [ Html.td [ Attr.class "sd-item-cell" ] (row.item |> Maybe.map (\ref -> [ itemLink ref ]) |> Maybe.withDefault []) ]

                    else
                        []
            in
            Html.div [ Attr.class "sd-table-wrap" ]
                [ Html.table
                    [ Attr.classList [ ( "sd-table", True ), ( "sd-rule-below", t.ruleBelow ) ] ]
                    [ Html.tbody []
                        (List.map
                            (\row ->
                                Html.tr
                                    (Attr.classList [ ( "sd-rule-above", row.rule ) ]
                                        :: (row.item |> Maybe.map (\ref -> [ Attr.id ref.id ]) |> Maybe.withDefault [])
                                    )
                                    ((List.indexedMap
                                        (\i cell ->
                                            let
                                                wrap =
                                                    List.drop i t.columns |> List.head |> Maybe.map .wrap |> Maybe.withDefault False
                                            in
                                            Html.td
                                                [ Attr.style "text-align" cell.align
                                                , Attr.colspan cell.span
                                                , Attr.classList [ ( "sd-wrap", wrap ) ]
                                                ]
                                                (inlines cell.content)
                                        )
                                        row.cells
                                     )
                                        ++ itemCell row
                                    )
                            )
                            t.rows
                        )
                    ]
                ]

        Pre v ->
            Html.pre [ Attr.class "sd-pre" ] [ Html.text v ]

        RuleGroup g ->
            Html.div [ Attr.class "sd-rulegroup" ]
                [ Html.span [ Attr.class "sd-rulegroup-title" ] (inlines g.title)
                , Html.span [ Attr.class "sd-judgement" ] (math g.judgement)
                ]

        RuleBlock r ->
            Html.div [ Attr.class "sd-rule", Attr.id r.id ]
                [ Html.div [ Attr.class "sd-rule-math" ] (math r.math)
                , Html.a [ Attr.class "sd-rule-num", Attr.href (ruleHref r.slug), Attr.title ("Rule " ++ String.fromInt r.number ++ ": " ++ r.slug) ]
                    [ Html.text ("(" ++ String.fromInt r.number ++ ")") ]
                ]

        Comments items ->
            Html.div [ Attr.class "sd-comments" ]
                (Html.div [ Attr.class "sd-comments-head" ] [ Html.text "Comments:" ]
                    :: List.map
                        (\c ->
                            Html.div [ Attr.class "sd-comment" ]
                                [ Html.a [ Attr.class "sd-comment-num", Attr.href (ruleHref c.rule) ]
                                    [ Html.text ("(" ++ (c.number |> Maybe.map String.fromInt |> Maybe.withDefault "?") ++ ")") ]
                                , Html.div [ Attr.class "sd-comment-body" ] (blocks c.content)
                                ]
                        )
                        items
                )

        RawBlock tex ->
            Html.pre [ Attr.class "sd-raw" ] [ Html.text tex ]
