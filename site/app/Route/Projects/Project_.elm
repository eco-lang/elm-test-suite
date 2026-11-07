module Route.Projects.Project_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

import BackendTask exposing (BackendTask)
import Data exposing (Compiler, Project, Report, Status(..), TestRow)
import Discuss
import DiscussionsView
import Effect exposing (Effect)
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html exposing (Html)
import Html.Attributes as Attr
import Html.Events as Events
import Pages.Url
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatefulRoute)
import Shared
import Site
import Ui
import UrlPath exposing (UrlPath)
import View exposing (View)


type Filter
    = All
    | FailingSomewhere
    | Differing
    | FailingUnder Int


type alias Model =
    { filter : Filter
    , search : String
    }


type Msg
    = SetFilter Filter
    | SetSearch String


type alias RouteParams =
    { project : String }


type alias Data =
    { report : Report
    , project : Project
    }


type alias ActionData =
    {}


route : StatefulRoute RouteParams Data ActionData Model Msg
route =
    RouteBuilder.preRender
        { head = head
        , pages = pages
        , data = data
        }
        |> RouteBuilder.buildWithLocalState
            { view = view
            , init = \_ _ -> ( { filter = All, search = "" }, Effect.none )
            , update = update
            , subscriptions = \_ _ _ _ -> Sub.none
            }


pages : BackendTask FatalError (List RouteParams)
pages =
    Data.report
        |> BackendTask.map (.projects >> List.map (\p -> { project = p.name }))


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map2 Data Data.report (Data.project params.project)


update : App Data ActionData RouteParams -> Shared.Model -> Msg -> Model -> ( Model, Effect Msg )
update _ _ msg model =
    case msg of
        SetFilter filter ->
            ( { model | filter = filter }, Effect.none )

        SetSearch search ->
            ( { model | search = search }, Effect.none )


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
        , description = app.data.project.description
        , locale = Nothing
        , title = app.data.project.name ++ " · " ++ Site.title
        }
        |> Seo.website


keep : Model -> TestRow -> Bool
keep model row =
    let
        statuses =
            List.map .status row.outcomes

        matchesFilter =
            case model.filter of
                All ->
                    True

                FailingSomewhere ->
                    List.member Fail statuses

                Differing ->
                    case statuses of
                        first :: rest ->
                            List.any ((/=) first) rest

                        [] ->
                            False

                FailingUnder i ->
                    List.drop i statuses |> List.head |> (==) (Just Fail)

        needle =
            String.toLower (String.trim model.search)
    in
    matchesFilter
        && (String.isEmpty needle
                || String.contains needle (String.toLower row.name)
                || String.contains needle (String.toLower row.summary)
           )


view : App Data ActionData RouteParams -> Shared.Model -> Model -> View (PagesMsg Msg)
view app shared model =
    let
        project =
            app.data.project

        key =
            "p:" ++ project.name

        compilers =
            app.data.report.compilers

        shown =
            List.filter (keep model) project.tests

        chip filter label =
            Html.button
                [ Attr.class
                    (if model.filter == filter then
                        "ts-chip ts-chip-active"

                     else
                        "ts-chip"
                    )
                , Events.onClick (PagesMsg.fromMsg (SetFilter filter))
                ]
                [ Html.text label ]
    in
    { title = project.name ++ " · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ] [ Route.link [] [ Html.text "Results" ] Route.Index, Html.text " / " ]
        , Html.h1 [ Attr.class "ts-h1" ] [ Html.text project.name ]
        , Html.p [ Attr.class "ts-lede" ] [ Html.text project.description ]
        , Html.p [ Attr.class "ts-small" ] [ Html.a [ Attr.href "#discussions" ] [ Html.text "Discussions of this project and its tests ↓" ] ]
        , Html.div [ Attr.class "ts-filters" ]
            ([ chip All ("All " ++ String.fromInt (List.length project.tests))
             , chip FailingSomewhere "Failing anywhere"
             , chip Differing "Outcome differs"
             ]
                ++ List.indexedMap (\i c -> chip (FailingUnder i) ("Failing under " ++ c.name)) compilers
                ++ [ Html.input
                        [ Attr.class "ts-input"
                        , Attr.placeholder "Search tests"
                        , Attr.type_ "search"
                        , Attr.value model.search
                        , Events.onInput (PagesMsg.fromMsg << SetSearch)
                        ]
                        []
                   ]
            )
        , Html.p [ Attr.class "ts-muted ts-small" ]
            [ Html.text ("Showing " ++ String.fromInt (List.length shown) ++ " of " ++ String.fromInt (List.length project.tests) ++ " tests. Hover over a badge for the reason.") ]
        , Html.div [ Attr.class "ts-scroll" ]
            [ Html.table [ Attr.class "ts-table" ]
                [ Html.thead []
                    [ Html.tr []
                        (Html.th [] [ Html.text "Test" ]
                            :: List.map (\c -> Html.th [ Attr.class "ts-center" ] [ Html.text c.name ]) compilers
                        )
                    ]
                , Html.tbody [] (List.map (testRow project.name) shown)
                ]
            ]
        , DiscussionsView.section
            { category = Discuss.Tests
            , key = key
            , noun = "project"
            , url = Site.canonicalUrl ++ Route.toString (Route.Projects__Project_ { project = project.name })
            , context = "The project " ++ project.name ++ ": " ++ project.description
            }
            (\k -> k == key || String.startsWith ("t:" ++ project.name ++ "/") k)
            shared.discussions
        ]
    }


testRow : String -> TestRow -> Html msg
testRow projectName row =
    Html.tr []
        (Html.td []
            [ Route.link [ Attr.class "ts-test-name" ]
                [ Html.text row.name ]
                (Route.Projects__Project___Test_ { project = projectName, test = row.name })
            , if row.compileError then
                Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text "  (must not compile)" ]

              else
                Html.text ""
            , Html.div [ Attr.class "ts-summary" ] [ Html.text (truncate 220 row.summary) ]
            ]
            :: List.map
                (\o -> Html.td [ Attr.class "ts-center" ] [ Ui.statusBadgeWithReason o.status o.reason ])
                row.outcomes
        )


truncate : Int -> String -> String
truncate n s =
    if String.length s > n then
        String.left (n - 1) s ++ "…"

    else
        s
