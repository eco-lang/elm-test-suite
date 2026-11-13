module Route.Results exposing (ActionData, Data, Model, Msg, RouteParams, route)

import BackendTask exposing (BackendTask)
import Content
import Data exposing (Compiler, Differing, ProjectSummary, Report)
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
import Ui
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


type alias Data =
    { report : Report
    , intro : String
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data = data
        }
        |> RouteBuilder.buildNoState { view = view }


data : BackendTask FatalError Data
data =
    BackendTask.map2 (\r i -> { report = r, intro = i }) Data.report (Content.load "results")


head : App Data ActionData RouteParams -> List Head.Tag
head _ =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = "Results of the Elm compiler end-to-end test suite under each compiler"
        , locale = Nothing
        , title = Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app _ =
    let
        report =
            app.data.report
    in
    { title = Site.title ++ ": results"
    , body =
        [ Html.h1 [ Attr.class "ts-h1" ] [ Html.text "Results" ]
        , Html.a [ Attr.class "ts-jump", Attr.href "#differing" ]
            [ Html.strong []
                [ Html.text
                    (case List.length report.differing of
                        1 ->
                            "1 test has"

                        n ->
                            String.fromInt n ++ " tests have"
                    )
                ]
            , Html.text " a different outcome under different compilers. "
            , Html.span [ Attr.class "ts-jump-action" ] [ Html.text "See the differences ↓" ]
            ]
        , Html.div [] (Content.view Content.Site Content.none app.data.intro)
        , Html.section [ Attr.class "ts-section" ]
            [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "Compilers" ]
            , Html.div [ Attr.class "ts-cards" ] (List.map compilerCard report.compilers)
            ]
        , Html.section [ Attr.class "ts-section" ]
            [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "By project" ]
            , Html.p [ Attr.class "ts-muted ts-small" ] [ Html.text "Passed / failed (/ skipped). Choose a project to see its tests." ]
            , Html.div [ Attr.class "ts-scroll" ] [ summaryTable "Project" (\name -> Route.Projects__Project_ { project = name }) report report.projects ]
            ]
        , Html.section [ Attr.class "ts-section", Attr.id "tags" ]
            [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "By tag" ]
            , Html.p [ Attr.class "ts-muted ts-small" ] [ Html.text "Passed / failed (/ skipped). A tag gathers tests across projects; choose one to see its tests." ]
            , Html.div [ Attr.class "ts-scroll" ] [ summaryTable "Tag" (\name -> Route.Tags__Tag_ { tag = name }) report report.tags ]
            ]
        , Html.section [ Attr.class "ts-section", Attr.id "differing" ]
            [ Html.h2 [ Attr.class "ts-h2" ]
                [ Html.text ("Tests whose outcome differs (" ++ String.fromInt (List.length report.differing) ++ ")") ]
            , Html.p [ Attr.class "ts-muted ts-small" ] [ Html.text "Hover over a badge for the reason; choose a test for its output." ]
            , if List.isEmpty report.differing then
                Html.p [] [ Html.text "None: every test has the same outcome under every compiler." ]

              else
                Html.div [ Attr.class "ts-scroll" ] [ differingTable report ]
            ]
        ]
    }


compilerCard : Compiler -> Html msg
compilerCard compiler =
    Html.div [ Attr.class "ts-card" ]
        [ Html.h3 [ Attr.class "ts-h3" ] [ Html.text compiler.name ]
        , Html.div [ Attr.class "ts-muted ts-small" ] [ Html.text compiler.description ]
        , Html.div [ Attr.class "ts-big-number" ] [ Html.text (Ui.percent compiler.counts) ]
        , Html.div [ Attr.class "ts-small" ]
            [ Html.span [ Attr.class "ts-text-pass" ] [ Html.text (String.fromInt compiler.counts.pass ++ " passed") ]
            , Html.text " · "
            , Html.span [ Attr.class "ts-text-fail" ] [ Html.text (String.fromInt compiler.counts.fail ++ " failed") ]
            , if compiler.counts.skip > 0 then
                Html.text (" · " ++ String.fromInt compiler.counts.skip ++ " skipped")

              else
                Html.text ""
            ]
        , Ui.bar compiler.counts
        ]


{-| The totals of each project, or of each tag, with a link to its page.
-}
summaryTable : String -> (String -> Route.Route) -> Report -> List ProjectSummary -> Html msg
summaryTable heading toRoute report rows =
    Html.table [ Attr.class "ts-table" ]
        [ Html.thead []
            [ Html.tr []
                (Html.th [] [ Html.text heading ]
                    :: Html.th [ Attr.class "ts-num" ] [ Html.text "Tests" ]
                    :: List.map (\c -> Html.th [] [ Html.text c.name ]) report.compilers
                )
            ]
        , Html.tbody [] (List.map (summaryRow toRoute) rows)
        ]


summaryRow : (String -> Route.Route) -> ProjectSummary -> Html msg
summaryRow toRoute project =
    Html.tr []
        (Html.td []
            [ Route.link [] [ Html.strong [] [ Html.text project.name ] ] (toRoute project.name)
            , Html.div [ Attr.class "ts-summary" ] [ Html.text project.description ]
            ]
            :: Html.td [ Attr.class "ts-num" ] [ Html.text (String.fromInt project.total) ]
            :: List.map (\counts -> Html.td [ Attr.class "ts-num" ] (Ui.countsCell counts)) project.counts
        )


differingTable : Report -> Html msg
differingTable report =
    Html.table [ Attr.class "ts-table" ]
        [ Html.thead []
            [ Html.tr []
                (Html.th [] [ Html.text "Test" ]
                    :: List.map (\c -> Html.th [ Attr.class "ts-center" ] [ Html.text c.name ]) report.compilers
                )
            ]
        , Html.tbody [] (List.map differingRow report.differing)
        ]


differingRow : Differing -> Html msg
differingRow d =
    Html.tr []
        (Html.td []
            [ Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text (d.project ++ " / ") ]
            , Route.link [ Attr.class "ts-test-name" ]
                [ Html.text d.test ]
                (Route.Projects__Project___Test_ { project = d.project, test = d.test })
            ]
            :: List.map (\s -> Html.td [ Attr.class "ts-center" ] [ Ui.statusBadge s ]) d.outcomes
        )
