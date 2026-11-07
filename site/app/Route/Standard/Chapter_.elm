module Route.Standard.Chapter_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One chapter (or the preface, or an appendix) of The Definition of Standard Elm.
-}

import BackendTask exposing (BackendTask)
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html exposing (Html)
import Html.Attributes as Attr
import Pages.Url
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Block(..), Chapter, ChapterSummary, Index)
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    { chapter : String }


{-| `index` and `chapter` are used only inside `View.freeze`, so elm-pages leaves them out of the
data sent to the browser; the page title and description are kept apart for that reason. `slug` is the item's
name as the book writes it, for the key of its discussions: the address in the browser may not
keep its case (Netlify serves a mixed-case path at its lower-case form).
-}
type alias Data =
    { title : String
    , description : String
    , slug : String
    , index : Index
    , chapter : Chapter
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
        |> BackendTask.map (.chapters >> List.map (\c -> { chapter = c.summary.slug }))


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map2
        (\idx ch ->
            { title = titleText ch.summary ++ " · " ++ idx.title
            , description = titleText ch.summary ++ ", from " ++ idx.title ++ " (" ++ idx.edition ++ ")"
            , slug = ch.summary.slug
            , index = idx
            , chapter = ch
            }
        )
        Standard.index
        (Standard.chapter params.chapter)


titleText : ChapterSummary -> String
titleText ch =
    let
        plain =
            List.map
                (\i ->
                    case i of
                        Standard.Text t ->
                            t

                        Standard.Code c ->
                            c

                        _ ->
                            ""
                )
                ch.title
                |> String.concat
    in
    case ch.number of
        Just n ->
            n ++ " " ++ plain

        Nothing ->
            plain


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summary
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image =
            { url = Pages.Url.external ""
            , alt = app.data.title
            , dimensions = Nothing
            , mimeType = Nothing
            }
        , description = app.data.description
        , locale = Nothing
        , title = app.data.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app shared =
    let
        key =
            "ch:" ++ app.data.slug
    in
    { title = app.data.title
    , body =
        [ View.freeze (chapterView app.data.index app.data.chapter)
        , Html.div [ Attr.class "sd-book" ]
            [ DiscussionsView.section
                { category = Discuss.Standard
                , key = key
                , noun = "chapter"
                , url = Site.canonicalUrl ++ Render.chapterHref app.data.slug ""
                , context = app.data.description ++ "."
                }
                ((==) key)
                shared.discussions
            ]
        , View.freeze (chapterFoot app.data.index app.data.chapter)
        ]
    }


chapterView : Index -> Chapter -> Html msg
chapterView idx ch =
    let
        sections =
            idx.chapters
                |> List.filter (\c -> c.summary.slug == ch.summary.slug)
                |> List.concatMap .sections
                |> List.filter (\s -> s.level == 1)
    in
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx ch.summary
        , Html.h1 [ Attr.class "sd-chapter-title" ] (Render.chapterTitle ch.summary)
        , if List.length sections < 2 then
            Html.text ""

          else
            Html.nav [ Attr.class "sd-toc" ]
                [ Html.ol []
                    (List.map
                        (\s ->
                            Html.li []
                                [ Html.a [ Attr.href ("#" ++ s.id) ]
                                    ((case s.number of
                                        Just n ->
                                            Html.span [ Attr.class "sd-num" ] [ Html.text n ]

                                        Nothing ->
                                            Html.text ""
                                     )
                                        :: Render.inlines s.title
                                    )
                                ]
                        )
                        sections
                    )
                ]
        , Html.article [ Attr.class "sd-text" ] (Render.blocks ch.blocks)
        ]


chapterFoot : Index -> Chapter -> Html msg
chapterFoot idx ch =
    Html.div [ Attr.class "sd-book" ] [ pager ch, Render.licence idx ]


crumbs : Index -> ChapterSummary -> Html msg
crumbs idx ch =
    Html.div [ Attr.class "ts-crumbs" ]
        [ Html.a [ Attr.href (Route.toString Route.Standard) ] [ Html.text idx.title ]
        , Html.span [ Attr.class "sd-edition-chip" ] [ Html.text idx.edition ]
        , if String.isEmpty (Standard.chapterHeading ch) then
            Html.text ""

          else
            Html.text (" / " ++ Standard.chapterHeading ch)
        ]


pager : Chapter -> Html msg
pager ch =
    let
        link label maybe =
            case maybe of
                Just c ->
                    Html.a [ Attr.class "sd-pager-link", Attr.href (Render.chapterHref c.slug "") ]
                        [ Html.span [ Attr.class "sd-pager-label" ] [ Html.text label ]
                        , Html.span [] (Render.chapterTitle c)
                        ]

                Nothing ->
                    Html.span [] []
    in
    Html.nav [ Attr.class "sd-pager" ] [ link "Previous" ch.prev, link "Next" ch.next ]
