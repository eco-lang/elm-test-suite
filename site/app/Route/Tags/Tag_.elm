module Route.Tags.Tag_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

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
    { tag : String }


type alias Data =
    { report : Report
    , tag : Project
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
        |> BackendTask.map (.tags >> List.map (\t -> { tag = t.name }))


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map2 Data Data.report (Data.tag params.tag)


update : App Data ActionData RouteParams -> Shared.Model -> Msg -> Model -> ( Model, Effect Msg )
update _ _ msg model =
    ( TestList.update msg model, Effect.none )


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = app.data.tag.description
        , locale = Nothing
        , title = app.data.tag.name ++ " · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> Model -> View (PagesMsg Msg)
view app shared model =
    let
        tag =
            app.data.tag

        key =
            "tag:" ++ tag.name

        testKeys =
            List.map (\t -> "t:" ++ t.project ++ "/" ++ t.name) tag.tests
    in
    { title = tag.name ++ " · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ] [ Route.link [] [ Html.text "Results" ] Route.Index, Html.text " / tags / " ]
        , Html.h1 [ Attr.class "ts-h1" ] [ Html.text tag.name ]
        , Html.p [ Attr.class "ts-lede" ] [ Html.text tag.description ]
        , Html.p [ Attr.class "ts-small" ] [ Html.a [ Attr.href "#discussions" ] [ Html.text "Discussions of this tag and its tests ↓" ] ]
        ]
            ++ List.map (Html.map PagesMsg.fromMsg)
                (TestList.view { compilers = app.data.report.compilers, rows = tag.tests, showProject = True, hideTag = Just tag.name } model)
            ++ [ DiscussionsView.section
                    { category = Discuss.Tests
                    , key = key
                    , noun = "tag"
                    , url = Site.canonicalUrl ++ Route.toString (Route.Tags__Tag_ { tag = tag.name })
                    , context = "The tag " ++ tag.name ++ ": " ++ tag.description
                    }
                    (\k -> k == key || List.member k testKeys)
                    shared.discussions
               ]
    }
