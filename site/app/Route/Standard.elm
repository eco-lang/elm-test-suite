module Route.Standard exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| A Standard Definition of Elm?, its title page and contents.
-}

import BackendTask exposing (BackendTask)
import Content
import Dict
import Discuss
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
import Standard exposing (Index, IndexChapter, ItemKind(..))
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


{-| `index` is used only inside `View.freeze`, so elm-pages leaves it out of the data sent to the
browser; the page title and description are kept apart for that reason.
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
                    { title = idx.title ++ " · " ++ Site.title
                    , description = idx.title ++ " (" ++ idx.edition ++ "): a formal definition of the Elm language, with a page for every rule"
                    , index = idx
                    , intro = intro
                    }
                )
                Standard.index
                (Content.load "standard/front")
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
    , body = [ View.freeze (front app.data.index app.data.intro) ]
    }


{-| The front page: the book's title, its introduction (content/standard/front.md, with the
buttons and the counts filled in), and its contents.
-}
front : Index -> String -> Html msg
front idx intro =
    let
        part p =
            List.filter (\c -> c.summary.part == p) idx.chapters

        count kind =
            String.fromInt (List.length (List.filter (\it -> it.kind == kind) idx.items))

        actions =
            Html.div [ Attr.class "sd-actions" ]
                (List.filterMap identity
                    [ Just (Html.a [ Attr.class "sd-button", Attr.href (Route.toString Route.Standard__Rules) ] [ Html.text ("All " ++ String.fromInt (List.length idx.rules) ++ " rules") ])
                    , Just (Html.a [ Attr.class "sd-button", Attr.href (Route.toString Route.Standard__Proofs) ] [ Html.text "Lean proofs" ])
                    , idx.pdf
                        |> Maybe.map
                            (\pdf ->
                                Html.a [ Attr.class "sd-button sd-button-quiet", Attr.href ("/" ++ pdf) ] [ Html.text "Download the PDF" ]
                            )
                    ]
                )
    in
    Html.div [ Attr.class "sd-book sd-front" ]
        ([ Html.h1 [ Attr.class "sd-title" ] [ Html.text idx.title ]
         , Html.div [ Attr.class "sd-edition" ] [ Html.text idx.edition ]
         , Html.div [ Attr.class "sd-author" ] [ Html.text idx.author ]
         ]
            ++ Content.view Content.Book
                { vars =
                    Dict.fromList
                        [ ( "restrictions", count Restriction )
                        , ( "derivedForms", count DerivedForm )
                        , ( "basis", count BasisEntry )
                        , ( "figures", count FigureItem )
                        , ( "categoryUrl", Discuss.categoryUrl Discuss.Standard )
                        ]
                , slots = Dict.fromList [ ( "actions", actions ) ]
                }
                intro
            ++ [ Html.h2 [ Attr.class "sd-contents-head" ] [ Html.text "Contents" ]
               , Html.ol [ Attr.class "sd-contents" ] (List.map contentsEntry (part "front" ++ part "main"))
               , Html.h3 [ Attr.class "sd-contents-sub" ] [ Html.text "Appendices" ]
               , Html.ol [ Attr.class "sd-contents" ] (List.map contentsEntry (part "appendix"))
               , Render.licence idx
               ]
        )


contentsEntry : IndexChapter -> Html msg
contentsEntry ch =
    Html.li [ Attr.class "sd-contents-chapter" ]
        [ Html.a [ Attr.href (Render.chapterHref ch.summary.slug ""), Attr.class "sd-contents-title" ] (Render.chapterTitle ch.summary)
        , case ch.rules of
            Just ( first, last ) ->
                Html.span [ Attr.class "sd-contents-rules" ]
                    [ Html.a [ Attr.href (Route.toString Route.Standard__Rules ++ "#" ++ ch.summary.slug) ]
                        [ Html.text ("rules " ++ String.fromInt first ++ "–" ++ String.fromInt last) ]
                    ]

            Nothing ->
                Html.text ""
        , if List.isEmpty ch.sections then
            Html.text ""

          else
            Html.ol [ Attr.class "sd-contents-sections" ]
                (ch.sections
                    |> List.filter (\s -> s.level == 1)
                    |> List.map
                        (\s ->
                            Html.li []
                                [ Html.a [ Attr.href (Render.chapterHref ch.summary.slug s.id) ]
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
                )
        ]
