module Route.Standard exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| The Definition of Standard Elm: its title page and contents.
-}

import BackendTask exposing (BackendTask)
import Discuss
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
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data =
            Standard.index
                |> BackendTask.map
                    (\idx ->
                        { title = idx.title ++ " · " ++ Site.title
                        , description = idx.title ++ " (" ++ idx.edition ++ "): a formal definition of the Elm language, with a page for every rule"
                        , index = idx
                        }
                    )
        }
        |> RouteBuilder.buildNoState { view = view }


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
view app _ =
    { title = app.data.title
    , body = [ View.freeze (front app.data.index) ]
    }


front : Index -> Html msg
front idx =
    let
        part p =
            List.filter (\c -> c.summary.part == p) idx.chapters
    in
    Html.div [ Attr.class "sd-book sd-front" ]
        [ Html.h1 [ Attr.class "sd-title" ] [ Html.text idx.title ]
        , Html.div [ Attr.class "sd-edition" ] [ Html.text idx.edition ]
        , Html.div [ Attr.class "sd-author" ] [ Html.text idx.author ]
        , Html.p [ Attr.class "sd-lede" ]
            [ Html.text "A formal definition of the Elm language: its grammar, its static semantics (which programs are legal, and their types) and its dynamic semantics (what they do), as numbered inference rules in the manner of "
            , Html.em [] [ Html.text "The Definition of Standard ML" ]
            , Html.text ". Every rule has its own page and a permanent address, so that it can be cited, linked to and discussed."
            ]
        , Html.p [ Attr.class "sd-draft-note" ]
            [ Html.strong [] [ Html.text "Draft. " ]
            , Html.text "This edition is a draft for review. Many of its rulings are provisional, and rule numbers may change between editions; a rule's address, which uses its name, does not."
            ]
        , Html.div [ Attr.class "sd-actions" ]
            (List.filterMap identity
                [ Just (Html.a [ Attr.class "sd-button", Attr.href (Route.toString Route.Standard__Rules) ] [ Html.text ("All " ++ String.fromInt (List.length idx.rules) ++ " rules") ])
                , idx.pdf
                    |> Maybe.map
                        (\pdf ->
                            Html.a [ Attr.class "sd-button sd-button-quiet", Attr.href ("/" ++ pdf) ] [ Html.text "Download the PDF" ]
                        )
                ]
            )
        , let
            count kind =
                String.fromInt (List.length (List.filter (\it -> it.kind == kind) idx.items))
          in
          Html.p [ Attr.class "sd-also" ]
            [ Html.text "Also with a page each: "
            , Html.a [ Attr.href (Route.toString Route.Standard__Restrictions) ] [ Html.text (count Restriction ++ " restrictions") ]
            , Html.text ", "
            , Html.a [ Attr.href (Route.toString Route.Standard__DerivedForms) ] [ Html.text (count DerivedForm ++ " derived forms") ]
            , Html.text " and "
            , Html.a [ Attr.href (Route.toString Route.Standard__Basis) ] [ Html.text (count BasisEntry ++ " entries of the initial basis") ]
            , Html.text "."
            ]
        , Html.p [ Attr.class "sd-also" ]
            [ Html.strong [] [ Html.text "Take part. " ]
            , Html.text "Each of those pages, and each chapter, has a Discussions section: start a discussion of the item on GitHub with its Discuss link, and the discussion is shown on the page. See "
            , Html.a [ Attr.href (Route.toString Route.Standard__Discussions) ] [ Html.text "all the discussions" ]
            , Html.text ", or the "
            , Html.a [ Attr.href (Discuss.categoryUrl Discuss.Standard), Attr.target "_blank", Attr.rel "noopener noreferrer" ] [ Html.text "Standard category" ]
            , Html.text " of the repository's GitHub Discussions."
            ]
        , Html.h2 [ Attr.class "sd-contents-head" ] [ Html.text "Contents" ]
        , Html.ol [ Attr.class "sd-contents" ] (List.map contentsEntry (part "front" ++ part "main"))
        , Html.h3 [ Attr.class "sd-contents-sub" ] [ Html.text "Appendices" ]
        , Html.ol [ Attr.class "sd-contents" ] (List.map contentsEntry (part "appendix"))
        , Render.licence idx
        ]


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
