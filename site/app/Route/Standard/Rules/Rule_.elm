module Route.Standard.Rules.Rule_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One rule of A Standard Definition of Elm?, at an address made from its name.
-}

import BackendTask exposing (BackendTask)
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html exposing (Html)
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index, Rule, RuleLink)
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    { rule : String }


{-| `index` and `rule` are used only inside `View.freeze`, so elm-pages leaves them out of the data
sent to the browser; the page title and description are kept apart for that reason. `slug` is the item's
name as the book writes it, for the key of its discussions: the address in the browser may not
keep its case (Netlify serves a mixed-case path at its lower-case form).
-}
type alias Data =
    { title : String
    , description : String
    , slug : String
    , index : Index
    , rule : Rule
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.preRender
        { head = head
        , pages = pages
        , data = data
        }
        |> RouteBuilder.buildNoState { view = view }


pages : BackendTask FatalError (List RouteParams)
pages =
    Standard.index
        |> BackendTask.map (.rules >> List.map (\r -> { rule = r.slug }))


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map2
        (\idx r ->
            { title = "Rule " ++ String.fromInt r.number ++ " (" ++ r.slug ++ ") · " ++ idx.title
            , description = "Rule " ++ String.fromInt r.number ++ ", " ++ r.slug ++ ", of " ++ idx.title ++ " (" ++ idx.edition ++ ")"
            , slug = r.slug
            , index = idx
            , rule = r
            }
        )
        Standard.index
        (Standard.rule params.rule)


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = app.data.description
        , locale = Nothing
        , title = app.data.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app shared =
    let
        key =
            "r:" ++ app.data.slug
    in
    { title = app.data.title
    , body =
        [ View.freeze (ruleView app.data.index app.data.rule)
        , Html.div [ Attr.class "sd-book" ]
            [ DiscussionsView.section
                { category = Discuss.Standard
                , key = key
                , noun = "rule"
                , url = Site.canonicalUrl ++ Render.ruleHref app.data.slug
                , context = app.data.description ++ "."
                }
                ((==) key)
                shared.discussions
            ]
        , View.freeze (ruleFoot app.data.index app.data.rule)
        ]
    }


ruleView : Index -> Rule -> Html msg
ruleView idx r =
    Html.div [ Attr.class "sd-book" ]
        [ Html.div [ Attr.class "ts-crumbs" ]
            [ Html.a [ Attr.href (Route.toString Route.Standard) ] [ Html.text idx.title ]
            , Html.span [ Attr.class "sd-edition-chip" ] [ Html.text idx.edition ]
            , Html.text " / "
            , Html.a [ Attr.href (Render.chapterHref r.chapter.slug "") ] [ Html.text (Standard.chapterHeading r.chapter) ]
            , case r.section of
                Just s ->
                    Html.span []
                        [ Html.text " / "
                        , Html.a [ Attr.href (Render.chapterHref r.chapter.slug s.id) ]
                            (Html.text (Maybe.withDefault "" s.number ++ " ") :: Render.inlines s.title)
                        ]

                Nothing ->
                    Html.text ""
            ]
        , Html.h1 [ Attr.class "sd-chapter-title" ]
            [ Html.text ("Rule " ++ String.fromInt r.number)
            , Html.code [ Attr.class "sd-rule-slug" ] [ Html.text r.slug ]
            ]
        , case r.group of
            Just g ->
                Html.div [ Attr.class "sd-rulegroup" ]
                    [ Html.span [ Attr.class "sd-rulegroup-title" ] (Render.inlines g.title)
                    , Html.span [ Attr.class "sd-judgement" ] (Render.math g.judgement)
                    ]

            Nothing ->
                Html.text ""
        , Html.div [ Attr.class "sd-rule sd-rule-single" ]
            [ Html.div [ Attr.class "sd-rule-math" ] (Render.math r.math)
            , Html.span [ Attr.class "sd-rule-num" ] [ Html.text ("(" ++ String.fromInt r.number ++ ")") ]
            ]
        , Html.div [ Attr.class "sd-rule-actions" ]
            [ Html.a [ Attr.href (Render.chapterHref r.chapter.slug ("r-" ++ r.slug)) ] [ Html.text "Read it in its chapter" ]
            , Html.span [ Attr.class "ts-muted" ] [ Html.text "·" ]
            , Html.span [ Attr.class "ts-muted" ]
                [ Html.text "Permanent address: "
                , Html.code [] [ Html.text (Render.ruleHref r.slug) ]
                ]
            ]
        , if List.isEmpty r.comments then
            Html.text ""

          else
            Html.section [ Attr.class "ts-section" ]
                [ Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text "Comments" ]
                , Html.div [ Attr.class "sd-text" ] (List.concatMap Render.blocks r.comments)
                ]
        , if List.isEmpty r.referencedFrom then
            Html.text ""

          else
            Html.section [ Attr.class "ts-section" ]
                [ Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text "Referred to from" ]
                , Html.ul [ Attr.class "sd-list" ] (List.map Render.place r.referencedFrom)
                ]
        , Html.section [ Attr.class "ts-section" ]
            [ Html.details []
                [ Html.summary [] [ Html.text "TeX source" ]
                , Html.pre [ Attr.class "ts-pre" ]
                    [ Html.text
                        ("\\defnrule[r:"
                            ++ r.slug
                            ++ "]\n  {"
                            ++ r.premises
                            ++ "}\n  {"
                            ++ r.conclusion
                            ++ "}"
                        )
                    ]
                ]
            ]
        ]


ruleFoot : Index -> Rule -> Html msg
ruleFoot idx r =
    Html.div [ Attr.class "sd-book" ]
        [ Html.nav [ Attr.class "sd-pager" ] [ ruleLink "Previous rule" r.prev, ruleLink "Next rule" r.next ]
        , Render.licence idx
        ]


ruleLink : String -> Maybe RuleLink -> Html msg
ruleLink label maybe =
    case maybe of
        Just l ->
            Html.a [ Attr.class "sd-pager-link", Attr.href (Render.ruleHref l.slug) ]
                [ Html.span [ Attr.class "sd-pager-label" ] [ Html.text label ]
                , Html.span [] [ Html.text ("(" ++ String.fromInt l.number ++ ") "), Html.code [] [ Html.text l.slug ] ]
                ]

        Nothing ->
            Html.span [] []
