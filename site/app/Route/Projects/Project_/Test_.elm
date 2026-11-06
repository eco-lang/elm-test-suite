module Route.Projects.Project_.Test_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

import BackendTask exposing (BackendTask)
import Data exposing (Status(..), Test, TestResult)
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
import SyntaxHighlight
import Ui
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    { project : String
    , test : String
    }


type alias Data =
    Test


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
    Data.report
        |> BackendTask.andThen
            (\report ->
                report.projects
                    |> List.map
                        (\p ->
                            Data.project p.name
                                |> BackendTask.map (.tests >> List.map (\t -> { project = p.name, test = t.name }))
                        )
                    |> BackendTask.combine
                    |> BackendTask.map List.concat
            )


data : RouteParams -> BackendTask FatalError Data
data params =
    Data.test params.project params.test


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summary
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image =
            { url = Pages.Url.external ""
            , alt = Site.title
            , dimensions = Nothing
            , mimeType = Nothing
            }
        , description = String.left 200 app.data.doc
        , locale = Nothing
        , title = app.data.name ++ " · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app _ =
    let
        test =
            app.data
    in
    { title = test.name ++ " · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ]
            [ Route.link [] [ Html.text "Results" ] Route.Index
            , Html.text " / "
            , Route.link [] [ Html.text test.project ] (Route.Projects__Project_ { project = test.project })
            , Html.text " / "
            ]
        , Html.h1 [ Attr.class "ts-h1" ] [ Html.text test.name ]
        , Html.div [ Attr.class "ts-filters" ]
            (List.map
                (\r ->
                    Html.a [ Attr.href ("#" ++ r.compiler) ]
                        [ Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text (r.compiler ++ " ") ]
                        , Ui.statusBadge r.status
                        ]
                )
                test.results
            )
        , if List.isEmpty test.issues then
            Html.text ""

          else
            Html.p [ Attr.class "ts-small" ]
                (Html.text "Issue: "
                    :: List.intersperse (Html.text ", ")
                        (List.map (\url -> Html.a [ Attr.href url, Attr.rel "noopener" ] [ Html.text (issueLabel url) ]) test.issues)
                )
        , if String.isEmpty test.doc then
            Html.text ""

          else
            Html.div [ Attr.class "ts-card" ] [ Html.pre [ Attr.class "ts-doc" ] [ Html.text test.doc ] ]
        , Html.section [ Attr.class "ts-section" ]
            [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "Results" ]
            , Html.div [ Attr.class "ts-results" ] (List.map resultCard test.results)
            ]
        , Html.section [ Attr.class "ts-section" ]
            [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "Source" ]
            , Html.p [ Attr.class "ts-muted ts-small" ]
                [ Html.text "The "
                , Html.code [] [ Html.text "-- CHECK:" ]
                , Html.text " lines give the expected output."
                ]
            , source test.source
            ]
        ]
    }


{-| "elm/compiler#1246" for a GitHub issue URL.
-}
issueLabel : String -> String
issueLabel url =
    case String.split "/" (String.replace "https://github.com/" "" url) of
        [ owner, repo, _, number ] ->
            owner ++ "/" ++ repo ++ "#" ++ number

        _ ->
            url


resultCard : TestResult -> Html msg
resultCard r =
    let
        statusName =
            Data.statusLabel r.status

        pre text =
            Html.pre [ Attr.class "ts-pre" ] [ Html.text text ]
    in
    Html.div [ Attr.class ("ts-card ts-result-" ++ statusName), Attr.id r.compiler ]
        [ Html.div [ Attr.class "ts-result-head" ]
            [ Html.h3 [ Attr.class "ts-h3" ] [ Html.text r.compiler ]
            , Ui.statusBadge r.status
            , case r.ms of
                Just ms ->
                    Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text ("ran in " ++ String.fromInt ms ++ " ms") ]

                Nothing ->
                    Html.text ""
            ]
        , case r.status of
            Pass ->
                if String.isEmpty (String.trim r.output) then
                    Html.text ""

                else
                    Html.details [] [ Html.summary [] [ Html.text "Output" ], pre r.output ]

            _ ->
                if String.isEmpty r.message then
                    Html.text ""

                else
                    pre r.message
        ]


source : String -> Html msg
source code =
    case SyntaxHighlight.elm code of
        Ok highlighted ->
            Html.div [ Attr.class "ts-source" ]
                [ SyntaxHighlight.useTheme SyntaxHighlight.monokai
                , SyntaxHighlight.toBlockHtml (Just 1) highlighted
                ]

        Err _ ->
            Html.pre [ Attr.class "ts-pre" ] [ Html.text code ]
