module Route.Standard.Rules exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| Every rule of A Standard Definition of Elm?, by chapter and rule group.
-}

import BackendTask exposing (BackendTask)
import Content
import Dict
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
import Standard exposing (Index, IndexChapter, IndexRule)
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


{-| `index` is used only inside `View.freeze`, so it is not sent to the browser.
-}
type alias Data =
    { title : String
    , description : String
    , index : Index
    , intro : String
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data =
            BackendTask.map2
                (\idx intro ->
                    { title = "Rules · " ++ idx.title
                    , description = "The " ++ String.fromInt (List.length idx.rules) ++ " inference rules of " ++ idx.title
                    , index = idx
                    , intro = intro
                    }
                )
                Standard.index
                (Content.load "standard/rules")
        }
        |> RouteBuilder.buildNoState { view = view }


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
view app _ =
    { title = app.data.title
    , body = [ View.freeze (allRules app.data.index app.data.intro) ]
    }


allRules : Index -> String -> Html msg
allRules idx intro =
    Html.div [ Attr.class "sd-book" ]
        [ Html.div [ Attr.class "ts-crumbs" ]
            [ Html.a [ Attr.href (Route.toString Route.Standard) ] [ Html.text idx.title ]
            , Html.span [ Attr.class "sd-edition-chip" ] [ Html.text idx.edition ]
            , Html.text " / Rules"
            ]
        , Html.h1 [ Attr.class "sd-chapter-title" ] [ Html.text "Rules" ]
        , Html.div [] (Content.view Content.Book Content.none intro)
        , Html.div [] (List.filterMap (chapterRules idx) idx.chapters)
        , Render.licence idx
        ]


chapterRules : Index -> IndexChapter -> Maybe (Html msg)
chapterRules idx ch =
    case List.filter (\r -> r.chapter == ch.summary.slug) idx.rules of
        [] ->
            Nothing

        rules ->
            Just
                (Html.section [ Attr.class "ts-section", Attr.id ch.summary.slug ]
                    [ Html.h2 [ Attr.class "sd-h sd-h1" ]
                        [ Html.a [ Attr.href (Render.chapterHref ch.summary.slug "") ] (Render.chapterTitle ch.summary) ]
                    , Html.div [ Attr.class "ts-scroll" ]
                        [ Html.table [ Attr.class "ts-table sd-rules-table" ]
                            [ Html.thead []
                                [ Html.tr []
                                    [ Html.th [ Attr.class "ts-num" ] [ Html.text "No." ]
                                    , Html.th [] [ Html.text "Rule" ]
                                    , Html.th [] [ Html.text "Rule group" ]
                                    ]
                                ]
                            , Html.tbody [] (List.map ruleRow rules)
                            ]
                        ]
                    ]
                )


ruleRow : IndexRule -> Html msg
ruleRow r =
    Html.tr []
        [ Html.td [ Attr.class "ts-num" ] [ Html.text (String.fromInt r.number) ]
        , Html.td [] [ Html.a [ Attr.href (Render.ruleHref r.slug), Attr.class "ts-test-name" ] [ Html.text r.slug ] ]
        , Html.td [] (Render.inlines r.group)
        ]
