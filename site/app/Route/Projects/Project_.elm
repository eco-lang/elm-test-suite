module Route.Projects.Project_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

import BackendTask exposing (BackendTask)
import Data exposing (Project, Report)
import Discuss
import DiscussionsView
import Effect exposing (Effect)
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html exposing (Html)
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatefulRoute)
import Shared
import Site
import TestList
import UrlPath exposing (UrlPath)
import View exposing (View)


type alias Model =
    TestList.Model


type alias Msg =
    TestList.Msg


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
            , init = \_ _ -> ( TestList.init, Effect.none )
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
    ( TestList.update msg model, Effect.none )


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = app.data.project.description
        , locale = Nothing
        , title = app.data.project.name ++ " · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> Model -> View (PagesMsg Msg)
view app shared model =
    let
        project =
            app.data.project

        key =
            "p:" ++ project.name
    in
    { title = project.name ++ " · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ] [ Route.link [] [ Html.text "Results" ] Route.Results, Html.text " / " ]
        , Html.h1 [ Attr.class "ts-h1" ] [ Html.text project.name ]
        , Html.p [ Attr.class "ts-lede" ] [ Html.text project.description ]
        , Html.p [ Attr.class "ts-small" ] [ Html.a [ Attr.href "#discussions" ] [ Html.text "Discussions of this project and its tests ↓" ] ]
        ]
            ++ List.map (Html.map PagesMsg.fromMsg)
                (TestList.view { compilers = app.data.report.compilers, rows = project.tests, showProject = False, hideTag = Nothing } model)
            ++ [ DiscussionsView.section
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
